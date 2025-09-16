module Expr where

import Control.Applicative
import qualified Control.Monad as Monad
import qualified Control.Comonad as Comonad
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Char as Char
import Data.Foldable (foldrM, forM_)
import qualified Data.List as List
import Data.Maybe (mapMaybe)
import Data.String
import Ewe

newtype Var = MkVar { unVar :: String }
  deriving (Eq, Show)

instance IsString Var where
  fromString = MkVar

data Kind
  = Type
  deriving (Eq, Show)

data Type
  = TyVar Var
  | Fun [(Var, Kind)] [Type] Type
  deriving (Eq, Show) -- TODO: Do alpha equivalence

type TypePat = Type

data Expr
  = Var Var
  | Lam [Var] Expr
  | App Expr [Expr]
  deriving Show

type Ctx a = [(Var, a)]

emptyCtx :: Ctx a
emptyCtx = []

insertCtx :: Var -> a -> Ctx a -> Ctx a
insertCtx x v ctx = (x, v) : ctx

listInsertCtx :: [(Var, a)] -> Ctx a -> Ctx a
listInsertCtx [] ctx = ctx
listInsertCtx ((x, v) : xvs) ctx = (x, v) : listInsertCtx xvs ctx

lookupCtx :: Var -> Ctx a -> Maybe a
lookupCtx _ [] = Nothing
lookupCtx x ((x', v) : ctx)
  | x == x' = Just v
  | otherwise = lookupCtx x ctx

removeCtx :: Var -> Ctx a -> Ctx a
removeCtx _ [] = []
removeCtx x ((x', v) : ctx)
  | x == x' = ctx
  | otherwise = (x', v) : removeCtx x ctx

list2Ctx :: [(Var, a)] -> Ctx a
list2Ctx l = l

lookupAllCtx :: Var -> Ctx a -> [a]
lookupAllCtx _ [] = []
lookupAllCtx x ((x', a) : ctx)
  | x == x' = a : lookupAllCtx x ctx
  | otherwise = lookupAllCtx x ctx

allEq :: Eq a => [a] -> Bool
allEq [] = True
allEq (x : xs) = all (== x) xs

mergeCtx :: Eq a => Ctx a -> Ctx a -> Maybe (Ctx a)
mergeCtx a b =
  let
    ctx = a ++ b
    ctxVars = List.nub (map (\(x, _) -> x) ctx)
    ctxVals = map (\x -> lookupAllCtx x ctx) ctxVars
  in
    case all allEq ctxVals of
      True -> Just ctx
      False -> Nothing

{-
data TypeError
  = ArgumentLengthMismatch Expr Type
  | CheckMismatch Expr Type
  | AppArgLengthMismcatch [Expr] Type
  | MatchFail (Ctx ()) Type Type
  | FailedToMatch -- TODO: Improve error message here
  | FailedToMatchParameters Expr
  | CheckExpectedButGot Expr Type Type
  | UnboundVariable Var
  | CantSynth
  deriving Show
-}

-- type TC a = Either TypeError a

data AlphaEquiv = AlphaEquiv { ctxL :: Ctx Int, ctxR :: Ctx Int, level :: Int }

emptyAlphaEquiv :: AlphaEquiv
emptyAlphaEquiv = AlphaEquiv emptyCtx emptyCtx 0

makeAlphaEquiv :: Var -> Var -> AlphaEquiv -> AlphaEquiv
makeAlphaEquiv l r ae =
  AlphaEquiv
    (insertCtx l ae.level ae.ctxL)
    (insertCtx r ae.level ae.ctxR)
    (ae.level + 1)

alphaEquiv :: Var -> Var -> AlphaEquiv -> Bool
alphaEquiv x y ae
  | Just xl <- lookupCtx x ae.ctxL
  , Just yl <- lookupCtx y ae.ctxR = xl == yl
  | Nothing <- lookupCtx x ae.ctxL
  , Nothing <- lookupCtx y ae.ctxR = x == y
  | otherwise = False

-- typeError :: TypeError -> TC a
-- typeError = Left

{-
typeMatch :: Ctx () -> TypePat -> Type -> TC (Ctx Type)
typeMatch vars l r =
  case typeMatch' vars emptyAlphaEquiv l r of
    Nothing -> typeError (MatchFail vars l r)
    Just vals -> return vals

typeMatch' :: Ctx () -> AlphaEquiv -> TypePat -> Type -> Maybe (Ctx Type)
typeMatch' vars _ (TyVar x) t
  | Just () <- lookupCtx x vars = Just (insertCtx x t emptyCtx)
typeMatch' _ ae (TyVar x) (TyVar y)
  | alphaEquiv x y ae = Just emptyCtx
  | otherwise = Nothing
typeMatch' vars ae (Fun typeParams argTypes codomain) (Fun typeParams' argTypes' codomain') = do
  ae' <- foldr (\((x, _), (x', _)) ae -> makeAlphaEquiv x x' ae) ae <$> zipIfSameLength typeParams typeParams'
  paramCtxs <- Monad.join (mapM (\(argType, argType') -> typeMatch' vars ae' argType argType') <$> zipIfSameLength argTypes argTypes')
  codomainCtx <- typeMatch' vars ae' codomain codomain'
  foldrM mergeCtx codomainCtx paramCtxs
typeMatch' _ _ _ _ = Nothing

typeEq :: Type -> Type -> Bool
typeEq a b
  | Just _ <- typeMatch' emptyCtx emptyAlphaEquiv a b = True
  | otherwise = False
-}

zipIfSameLength :: [a] -> [b] -> Maybe [(a, b)]
zipIfSameLength [] [] = Just []
zipIfSameLength (a : al) (b : bl) = ((a, b) :) <$> zipIfSameLength al bl
zipIfSameLength _ _ = Nothing

varChar :: Parser l Char Char
varChar = is Char.isLetter

var :: Parser l Char Var
var = MkVar <$> some varChar

type TC l a = Either (ParseError l) a

checkDuplicates :: [Var] -> [Parsed l Var] -> TC l [Var]
checkDuplicates xs [] = Right xs
checkDuplicates xs (v : rest) = do
  xs' <-
    handle $ fmap
      (\x ->
        if elem x xs
        then Left (concat ["Variable `", show x, "` is a duplicate in the parameter list. Duplicates are not allowed."])
        else Right (xs ++ [x])
      )
      v
  checkDuplicates xs' rest

lamValidator :: Parsed l (Parsed l Var, [Parsed l Var]) -> (Ctx Kind -> Ctx Type -> Type -> TC l Expr) -> (Ctx Kind -> Ctx Type -> ([(Var, Kind)], [Type], Type) -> TC l Expr)
lamValidator vars body kindCtx typeCtx (typeParams, domains, codomain) = do
  params <-
    sequenceA $ fmap
      (\(firstVar, restVars) ->
        checkDuplicates [Comonad.extract firstVar] restVars
      )
      vars
  paramTypes <-
    handle $ fmap
      (\xs ->
        case zipIfSameLength xs domains of
          Just xTypes -> Right xTypes
          Nothing ->
            Left $ concat
              ["Expected "
              , show (length domains)
              , " parameter(s), but found "
              , show (length xs)
              , ", when checking lambda against type `"
              , show (Fun typeParams domains codomain)
              , "`"
              ]
      )
      params
  let kindCtx' = listInsertCtx typeParams kindCtx
  let typeCtx' = listInsertCtx paramTypes typeCtx
  bodyE <- body kindCtx' typeCtx' codomain -- TODO: Is there some capture avoiding substitution thing I'm forgetting here?
  return (Lam (map (\(x, _) -> x) paramTypes) bodyE)


lamCheckValidator :: Parsed l (Ctx Kind -> Ctx Type -> ([(Var, Kind)], [Type], Type) -> TC l Expr) -> (Ctx Kind -> Ctx Type -> Type -> TC l Expr)
lamCheckValidator lamv kindCtx typeCtx t =
  Monad.join $ handle $ fmap
    (\lamv' ->
      case t of
        Fun typeParams domains codomain -> Right (lamv' kindCtx typeCtx (typeParams, domains, codomain))
        _ -> Left (concat ["Expected an expression of type `", show t, "` but found a lambda"])
    )
    lamv

lam :: Parser l Char (Ctx Kind -> Ctx Type -> Type -> TC l Expr)
lam =
  fmap lamCheckValidator $ validate
    ( lamValidator
      <$> ( validate $ (\first rest -> (first, rest))
              <$> (tok '\\' *> whitespace *> validate var <* whitespace)
              <*> many (tok ',' *> whitespace *> validate var <* whitespace)
          )
      <*> (tok '-' *> tok '>' *> whitespace *> check)
    )

checkSynthValidator :: Parsed l (Ctx Kind -> Ctx Type -> TC l (Type, Expr)) -> (Ctx Kind -> Ctx Type -> Type -> TC l Expr)
checkSynthValidator ps kindCtx typeCtx t = do
  ps' <- sequenceA $ fmap
    (\s -> do
      (t', e) <- s kindCtx typeCtx
      if t == t'
      then return (Right e)
      else return (Left (concat ["Expected an expression of type `", show t, "`, but found one of type `", show t', "`"]))
    )
    ps
  handle ps'

checkSynth :: Parser l Char (Ctx Kind -> Ctx Type -> Type -> TC l Expr)
checkSynth = checkSynthValidator <$> validate synth

check :: Parser l Char (Ctx Kind -> Ctx Type -> Type -> TC l Expr)
check = lam <|> checkSynth

varValidate :: Parsed l Var -> (Ctx Kind -> Ctx Type -> TC l (Type, Expr))
varValidate v _ typeCtx =
  handle $ fmap
    (\x ->
      case lookupCtx x typeCtx of
        Just t -> Right (t, Var x)
        Nothing -> Left (concat ["Unbound identifier `", show x, "`"])
    )
    v

varSynth :: Parser l Char (Ctx Kind -> Ctx Type -> TC l (Type, Expr))
varSynth = varValidate <$> validate var

synth :: Parser l Char (Ctx Kind -> Ctx Type -> TC l (Type, Expr))
synth = varSynth

top :: Ctx Kind -> Ctx Type -> Type -> Parser l Char Expr
top kindCtx typeCtx t = throw $ (\c -> c kindCtx typeCtx t) <$> check

-- TODO: Capture avoiding substitution is messed up in following case
-- parse
--   (top
--     [("b", Type)]
--     [("b", TyVar "b")]
--     (Fun [("a", Type), ("b", Type)] [TyVar "a"] (TyVar "b"))
--   )
--   "\\x -> b"
