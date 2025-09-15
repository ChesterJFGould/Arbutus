module EweArrowized where

import Control.Arrow
import Control.Category
import Control.Monad
import Control.Monad.Fix (mfix)
import qualified Data.Char as Char

data Parser t d c where
  Arr :: (d -> c) -> Parser t d c
  Comp ::Parser t a b -> Parser t b c -> Parser t a c
  First :: Parser t d c -> Parser t (d, a) (c, a)
  Is :: (t -> Bool) -> Parser t d t
  Validate :: Parser t d (Either String c) -> Parser t d c
  Loop :: Parser t (d, a) (c, a) -> Parser t d c
  Fail :: Parser t d c
  Choice :: Parser t d c -> Parser t d c -> Parser t d c

instance Category (Parser t) where
  id = Arr (\x -> x)
  (.) = flip Comp

instance Arrow (Parser t) where
  arr = Arr
  first = First

instance ArrowZero (Parser t) where
  zeroArrow = Fail

instance ArrowPlus (Parser t) where
  (<+>) = Choice

instance ArrowLoop (Parser t) where
  loop = Loop

doLoop :: ((d, b) -> Maybe (c, b)) -> d -> Maybe c
doLoop f d = (\(c, _) -> c) <$> mfix (\(_, b) -> f (d, b))

parse :: Parser t d c-> [t] -> d -> Maybe c
parse p ts d
  | Just (f, _) <- parse' p ts = f d
  | otherwise = Nothing

parse' :: Parser t d c -> [t] -> Maybe (d -> Maybe c, [t])
parse' (Arr f) ts = Just (\d -> Just (f d), ts)
parse' (Comp f g) ts = do
  (ab, ts') <- parse' f ts
  (bc, ts'') <- parse' g ts'
  Just (ab >=> bc, ts'')
parse' (First p) ts = do
  (f, ts') <- parse' p ts
  return (\(d, b) -> (, b) <$> f d, ts')
parse' (Is p) (t : ts)
  | p t = Just (\_ -> Just t, ts)
  | otherwise = Nothing
parse' (Is _) [] = Nothing
parse' (Validate p) ts = do
  (v, ts') <- parse' p ts
  Just
    ( \d -> 
        case v d of
          Just (Right c) -> Just c
          _ -> Nothing
    , ts'
    )
parse' (Loop p) ts = do
  (f, ts') <- parse' p ts
  Just (doLoop f, ts')
parse' (Fail) _ = Nothing

whitespace :: Parser Char d Char
whitespace = proc _ -> do
  t <- Is (Char.isSpace) -< ()
  returnA -< t

many :: Parser t d c -> Parser t d [c]
many = _
