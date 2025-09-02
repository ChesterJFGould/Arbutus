module Expr where

import qualified Control.Monad as Monad
import qualified Data.Bifunctor as Bifunctor
import Data.Foldable (foldrM, forM_)
import qualified Data.List as List
import Data.String

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

data TypeError
  = ArgumentLengthMismatch Expr Type
  | CheckMismatch Expr Type
  | AppArgLengthMismcatch [Expr] Type
  | MatchFail (Ctx ()) Type Type
  | FailedToMatch -- TODO: Improve error message here
  | FailedToMatchParameters Expr
  | CheckExpectedButGot Expr Type Type
  | UnboundVariable Var
  deriving Show

type TC a = Either TypeError a

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

typeError :: TypeError -> TC a
typeError = Left

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

zipIfSameLength :: [a] -> [b] -> Maybe [(a, b)]
zipIfSameLength [] [] = Just []
zipIfSameLength (a : al) (b : bl) = ((a, b) :) <$> zipIfSameLength al bl
zipIfSameLength _ _ = Nothing

-- Separate expressions into synths and checks during check
separateCheck :: [(Expr, Type)] -> ([(Expr, Type)], [(Expr, Type)])
separateCheck [] = ([], [])
separateCheck ((Var x, t) : l) = Bifunctor.first ((Var x, t) :) (separateCheck l)
separateCheck ((App f args, t) : l) = Bifunctor.second ((App f args, t) :) (separateCheck l)
separateCheck ((Lam params body, t) : l) = Bifunctor.second ((Lam params body, t) :) (separateCheck l)

-- Separate expressions into synths and checks during synth
separateSynth :: [(Expr, Type)] -> ([(Expr, Type)], [(Expr, Type)])
separateSynth [] = ([], [])
separateSynth ((Var x, t) : l) = Bifunctor.first ((Var x, t) :) (separateCheck l)
separateSynth ((App f args, t) : l) = Bifunctor.first ((App f args, t) :) (separateCheck l)
separateSynth ((Lam params body, t) : l) = Bifunctor.second ((Lam params body, t) :) (separateCheck l)

instantiate :: Ctx Type -> Type -> Type
instantiate types (TyVar x)
  | Just t <- lookupCtx x types = t
  | otherwise = TyVar x
instantiate types (Fun typeParams paramTypes codomain) =
  let
    -- TODO: Definitely an error, need to do capture avoiding substitution
    types' = foldr (\(x, _) types -> removeCtx x types) types typeParams
  in
    Fun typeParams (map (instantiate types') paramTypes) (instantiate types' codomain)

check :: Ctx Kind -> Ctx Type -> Expr -> Type -> TC ()
check kindCtx typeCtx (Lam params body) (Fun typeParams paramTypes codomain)
  | length params == length paramTypes =
      check
        (listInsertCtx typeParams kindCtx)
        (listInsertCtx (zip params paramTypes) typeCtx)
        body
        codomain
  | otherwise = typeError (ArgumentLengthMismatch (Lam params body) (Fun typeParams paramTypes codomain))
check _ _ (Lam params body) t = typeError (CheckMismatch (Lam params body) t)
check kindCtx typeCtx (App f args) t = do
  fType <- synth kindCtx typeCtx f
  case fType of
    Fun typeParams paramTypes codomain
        -- Check arg lengths line up
      | Just argTypes <- zipIfSameLength args paramTypes -> do
        let
          patternVarsCtx :: Ctx ()
          patternVarsCtx = list2Ctx (map (\(x, _) -> (x, ())) typeParams)
        -- Match codomain
        codomainValsCtx <- typeMatch patternVarsCtx codomain t
        -- Separate argTypes into synths and checks
        --   for now, put apps in checks here, and in synths in synth
        let (synthArgTypes, checkArgTypes) = separateCheck argTypes
        -- Match synths
        synthArgCtxs <-
          mapM
            (\(arg, argType) -> do
              argType' <- synth kindCtx typeCtx arg
              typeMatch patternVarsCtx argType argType'
            )
            synthArgTypes
        patternValsCtx <-
          case foldrM mergeCtx codomainValsCtx synthArgCtxs of
            Just ctx -> return ctx
            Nothing -> typeError FailedToMatch
        {-
        patternValsCtx'' <-
          foldrM
            (\(arg, argType) patternValsCtx'' -> do
              argType' <- synth kindCtx typeCtx arg
              typeMatch patternVarsCtx patternValsCtx'' argType argType'
            )
            patternValsCtx'
            synthArgTypes
        -}
        -- Check if all vars covered
        case sequence (map (\(x, _) -> lookupCtx x patternValsCtx) typeParams) of
          Nothing -> typeError (FailedToMatchParameters (App f args))
          Just _ ->
          -- Check checks
            forM_
              checkArgTypes
              (\(arg, argType) -> check kindCtx typeCtx arg (instantiate patternValsCtx argType))
      | otherwise -> typeError (AppArgLengthMismcatch args (Fun typeParams paramTypes codomain))
check kindCtx typeCtx e t = do
  t' <- synth kindCtx typeCtx e
  case typeEq t t' of
    True -> return ()
    False -> typeError (CheckExpectedButGot e t t')

synth :: Ctx Kind -> Ctx Type -> Expr -> TC Type
synth kindCtx typeCtx (Var x)
  | Just t <- lookupCtx x typeCtx = return t
  | otherwise = typeError (UnboundVariable x)
synth kindCtx typeCtx (App f args) = do
  fType <- synth kindCtx typeCtx f
  case fType of
    Fun typeParams paramTypes codomain
        -- Check arg lengths line up
      | Just argTypes <- zipIfSameLength args paramTypes -> do
        let
          patternVarsCtx :: Ctx ()
          patternVarsCtx = list2Ctx (map (\(x, _) -> (x, ())) typeParams)
        -- Separate argTypes into synths and checks
        --   for now, put apps in checks here, and in synths in synth
        let (synthArgTypes, checkArgTypes) = separateSynth argTypes
        -- Match synths
        synthArgCtxs <-
          mapM
            (\(arg, argType) -> do
              argType' <- synth kindCtx typeCtx arg
              typeMatch patternVarsCtx argType argType'
            )
            synthArgTypes
        patternValsCtx <-
          case foldrM mergeCtx emptyCtx synthArgCtxs of
            Just ctx -> return ctx
            Nothing -> typeError FailedToMatch
        {-
        patternValsCtx'' <-
          foldrM
            (\(arg, argType) patternValsCtx'' -> do
              argType' <- synth kindCtx typeCtx arg
              typeMatch patternVarsCtx patternValsCtx'' argType argType'
            )
            patternValsCtx'
            synthArgTypes
        -}
        -- Check if all vars covered
        case sequence (map (\(x, _) -> lookupCtx x patternValsCtx) typeParams) of
          Nothing -> typeError (FailedToMatchParameters (App f args))
          Just _ -> do
          -- Check checks
            forM_
              checkArgTypes
              (\(arg, argType) -> check kindCtx typeCtx arg (instantiate patternValsCtx argType))
            return (instantiate patternValsCtx codomain)
      | otherwise -> typeError (AppArgLengthMismcatch args (Fun typeParams paramTypes codomain))
