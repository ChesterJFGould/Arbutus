{-# LANGUAGE GADTs, ApplicativeDo, DerivingVia, ImpredicativeTypes #-}
module Ewe (Parser, Validator, handle, validate, is, tok, validatorJoin, whitespace, startValidation, validatorBind, parse, parseFile, parseFilePrintError)  where

import Control.Applicative
import Control.Comonad
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Char as Char
import System.IO

data Validator srcloc a = Validator srcloc (Either String a)

instance Functor (Validator srcloc) where
  fmap f (Validator l v) = Validator l (fmap f v)

handle :: Validator srcloc (Either String a) -> Validator srcloc a
handle (Validator l (Right (Left err))) = Validator l (Left err)
handle (Validator l (Left err)) = Validator l (Left err)
handle (Validator l (Right (Right a))) = Validator l (Right a)

validatorJoin :: Validator srcloc (Validator srcloc a) -> Validator srcloc a
validatorJoin (Validator l (Left err)) = Validator l (Left err)
validatorJoin (Validator _ (Right v)) = v

validatorBind :: Validator l a -> (a -> Validator l b) -> Validator l b
validatorBind a f = validatorJoin (f <$> a)

data Parser l t a where
  Pure :: a -> Parser l t a
  -- Bind :: Parser l t b -> (b -> Parser l t a) -> Parser lt a
  App :: Parser l t (a -> b) -> Parser l t a -> Parser l t b
  Alt :: Parser l t a -> Parser l t a -> Parser l t a
  Is :: (t -> Bool) -> Parser l t t
  Fail :: Parser l t a
  -- The point of Validate is to take a parser which returns a function from some context to the actual parser output or an error,
  -- and then turn it into a parser which returns a function which when applied to the context, turns the error into a nice parser error
  -- pointing to the piece of text which the validation function was originally parsed.
  -- The problem to solve is what the output type of the returned validation function is.
  -- If it is (b -> Parser t a), then this implies that it could potentially consume some input, which it won't
  --   Maybe just go with this for now and figure out something nicer later?
  --   This is actually useless, since this functionality is derivable
  --   validate :: Parser t (b -> Either String a) -> Parser t (b -> Parser t a)
  --   validate p = do
  --     validator <- p
  --     return \b ->
  --       case validator b of
  --         Left _ -> Fail
  --         Right a -> Pure a
  -- Maybe we can fix this by using arrowized parsers instead of applicative?
  --   See EweArrowized.hs
  StartValidation :: Parser l t a -> Parser l t (Validator l a)
  Validate :: Parser l t (Validator l a) -> Parser l t a

-- bind :: Parser t a -> (a -> Parser t b) -> Parser t b
-- bind (Pure a) k = k a
-- bind a k = Bind a k

instance Functor (Parser l t) where
  fmap f a = App (Pure f) a

instance Applicative (Parser l t) where
  pure = Pure
  -- f <*> a = bind f (\fv -> bind a (\av -> Pure (fv av)))
  (<*>) = App

-- instance Monad (Parser t) where
--   a >>= f = bind a f

instance Alternative (Parser l t) where
  empty = Fail
  (<|>) = Alt

acceptsEmpty :: Parser l t a -> Bool
acceptsEmpty (Pure _) = True
acceptsEmpty (App f a) = acceptsEmpty f && acceptsEmpty a
acceptsEmpty (Alt a b) = acceptsEmpty a || acceptsEmpty b
acceptsEmpty (Is _) = False
acceptsEmpty (Fail) = False
acceptsEmpty (StartValidation p) = acceptsEmpty p
acceptsEmpty (Validate p) = acceptsEmpty p

acceptsTok :: Parser l t a -> t -> Bool
acceptsTok (Pure _) _ = True
acceptsTok (App f a) t
  | acceptsEmpty f = acceptsTok a t
  | otherwise = acceptsTok f t
acceptsTok (Alt a b) t = acceptsTok a t || acceptsTok b t
acceptsTok (Is p) t = p t
acceptsTok (Fail) _ = False
acceptsTok (StartValidation p) t = acceptsTok p t
acceptsTok (Validate p) t = acceptsTok p t

parse :: Show t => Parser () t a -> [t] -> Either String (a, [t])
parse (Pure a) ts = Right (a, ts)
parse (App f a) ts = do
  (fv, ts') <- parse f ts
  (av, ts'') <- parse a ts'
  return (fv av, ts'')
parse (Alt a b) (t : ts)
  | acceptsTok a t = parse a (t : ts)
  | otherwise = parse b (t : ts)
parse (Alt a b) []
  | Right av <- parse a [] = Right av
  | otherwise = parse b []
parse (Is p) (t : ts)
  | p t = Right (t, ts)
  | otherwise = Left (concat ["Unexpected token `", show t, "`"])
parse (Is _) [] = Left "Unexpected end of input"
parse (Fail) _ = Left "Failed to parse"
parse (StartValidation p) ts = do
  (a, ts') <- parse p ts
  return (Validator () (Right a), ts')
parse (Validate p) ts = do
  (validator, ts') <- parse p ts
  case validator of
    (Validator _ (Left err)) -> Left err
    (Validator _ (Right a)) -> Right (a, ts')

data FilePos = FilePos { line :: Int, col :: Int }
  deriving Show

data FileRange = FileRange { start :: FilePos, end :: FilePos }
  deriving Show

data FileError = FileError { range :: FileRange, msg :: String }

advanceFilePos :: Char -> FilePos -> FilePos
advanceFilePos '\n' fp = FilePos (fp.line + 1) 0
advanceFilePos _ fp = FilePos (fp.line) (fp.col + 1)

parseFilePrintError :: Parser FileRange Char a -> FilePath -> IO (Maybe a)
parseFilePrintError p path = do
  aOrErr <- parseFile p path
  case aOrErr of
    Left err -> err >> return Nothing
    Right a -> return (Just a)

parseFile :: Parser FileRange Char a -> FilePath -> IO (Either (IO ()) a)
parseFile p path = do
  pvOrErr <- withFile path ReadMode (parseFile' p (FilePos 0 0))
  case pvOrErr of
    Left err -> return (Left (printFileError err path))
    Right (pv, _) -> return (Right pv)

parseFile' :: Parser FileRange Char a -> FilePos -> Handle -> IO (Either FileError (a, FilePos))
parseFile' (Pure a) fp _ = return (Right (a, fp))
parseFile' (App f a) fp h = do
  fvOrErr <- parseFile' f fp h
  case fvOrErr of
    Left err -> return (Left err)
    Right (fv, fp') -> do
      avOrErr <- parseFile' a fp' h
      case avOrErr of
        Left err -> return (Left err)
        Right (av, fp'') -> return (Right (fv av, fp''))
parseFile' (Alt a b) fp h = do
  eof <- hIsEOF h
  if eof
  then
    if acceptsEmpty a
    then parseFile' a fp h
    else parseFile' b fp h
  else do
    c <- hLookAhead h
    if acceptsTok a c
    then parseFile' a fp h
    else parseFile' b fp h
parseFile' (Is p) fp h = do
  eof <- hIsEOF h
  if eof
  then return (Left (FileError (FileRange fp fp) "Unexpected end-of-file"))
  else do
    c <- hGetChar h
    if p c
    then return (Right (c, advanceFilePos c fp))
    else return (Left (FileError (FileRange fp fp) (concat ["Unexpected character ", show c])))
parseFile' (Fail) fp _ = return (Left (FileError (FileRange fp fp) "Parsing failed"))
parseFile' (StartValidation p) start h = do
  pvOrErr <- parseFile' p start h
  case pvOrErr of
    Left err -> return (Left err)
    Right (pv, end) -> return (Right (Validator (FileRange start end) (Right pv), end))
parseFile' (Validate p) fp h = do
  pvOrErr <- parseFile' p fp h
  case pvOrErr of
    Left err -> return (Left err)
    Right (Validator range (Left msg), _) -> return (Left (FileError range msg))
    Right (Validator _ (Right pv), fp') -> return (Right (pv, fp'))


printFileError :: FileError -> FilePath -> IO ()
printFileError err path = do
  hPutStrLn stderr (concat ["Error: ", err.msg])
  hPutStrLn stderr ""
  hPrintFileRange stderr err.range path

hPrintFileRange :: Handle -> FileRange -> FilePath -> IO ()
hPrintFileRange herr range path = do
  h <- openFile path ReadMode
  failed <- hSeekToLine h range.start.line
  if failed
  then hClose h >> return ()
  else do
    mapM
      (\lineNo -> do
        line <- hGetLine h
        hPrintLine herr range lineNo line
      )
      [range.start.line .. range.end.line]
    return ()

hPrintLine :: Handle -> FileRange -> Int -> String -> IO ()
hPrintLine herr range lineNo line = do
  let lineNoStr = show (lineNo + 1)
  let lineNoTotalDigits = length (show (range.end.line + 1))
  let lineNoDigits = length lineNoStr
  let lineNoPadding = replicate (lineNoTotalDigits - lineNoDigits) ' '
  let lineNoTotalStr = lineNoPadding ++ lineNoStr
  let underline = lineRangeUnderscores range lineNo line
  hPutStrLn herr (concat [lineNoTotalStr, " | ", line])
  hPutStrLn herr (concat [replicate (length lineNoTotalStr) ' ', " | ", underline])

lineRangeUnderscores :: FileRange -> Int -> String -> String
lineRangeUnderscores range lineNo line =
  if lineNo == range.start.line && lineNo == range.end.line
  then
    concat
      [ replicate range.start.col ' '
      , replicate (range.end.col - range.start.col) '^'
      , replicate (length line - range.end.col) ' '
      ]
  else if lineNo == range.start.line
  then
    concat
      [ replicate range.start.col ' '
      , replicate (length line - range.start.col) '^'
      ]
  else if lineNo == range.end.line
  then
    concat
      [ replicate (range.end.col) '^'
      , replicate (length line - range.end.col) ' '
      ]
  else replicate (length line) '^'


hSeekToLine :: Handle -> Int -> IO Bool
hSeekToLine _ 0 = return False
hSeekToLine h l = do
  eof <- hIsEOF h
  if eof
  then return True
  else do
    c <- hGetChar h
    case c of
      '\n' -> hSeekToLine h (l - 1)
      _ -> hSeekToLine h l

is :: (t -> Bool) -> Parser l t t
is = Is

tok :: Eq t => t -> Parser l t ()
tok t = is (== t) *> pure ()

whitespace :: Parser l Char ()
whitespace = many (is Char.isSpace) *> pure ()

startValidation :: Parser l t a -> Parser l t (Validator l a)
startValidation = StartValidation

validate :: Parser l t (Validator l a) -> Parser l t a
validate = Validate
