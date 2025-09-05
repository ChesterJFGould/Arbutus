module Stlc where

import qualified Data.Char as Char
import Control.Applicative
import Ewe

data Var = MkVar String
  deriving (Eq, Show)

data Type
  = Nat
  | Fun Type Type
  deriving (Eq, Show)

data Expr
  = Var Var
  | Lam Var Expr
  | App Expr Expr
  deriving Show

type Ctx a = [(Var, a)]

emptyCtx :: Ctx a
emptyCtx = []

insertCtx :: Var -> a -> Ctx a -> Ctx a
insertCtx x v ctx = (x, v) : ctx

lookupCtx :: Var -> Ctx a -> Maybe a
lookupCtx _ [] = Nothing
lookupCtx x ((x', v) : ctx)
  | x == x' = Just v
  | otherwise = lookupCtx x ctx

varChar :: Parser Char Char
varChar = is Char.isLetter

var :: Parser Char Var
var = MkVar <$> some varChar

parens :: Parser Char a -> Parser Char a
parens p = do
  tok '('
  whitespace
  pv <- p
  whitespace
  tok ')'
  return pv


checkSynth :: Ctx Type -> Type -> Parser Char Expr
checkSynth ctx t = validate $ do
  (e, t') <- synth ctx
  if t == t'
  then pure (Right e)
  else pure (Left "types don't match")

lam :: Ctx Type -> Type -> Parser Char Expr
lam ctx (Fun d c) = do
  tok '\\'
  whitespace
  x <- var
  whitespace
  tok '-'
  tok '>'
  whitespace
  e <- check (insertCtx x d ctx) c
  return (Lam x e)
lam _ _ = empty

check :: Ctx Type -> Type -> Parser Char Expr
check ctx t = lam ctx t <|> parens (check ctx t) <|> checkSynth ctx t

synthVar :: Ctx Type -> Parser Char (Expr, Type)
synthVar ctx = validate $ do
  x <- var
  case lookupCtx x ctx of
    Nothing -> pure (Left "unbound variable")
    Just t -> pure (Right (Var x, t))

synth :: Ctx Type -> Parser Char (Expr, Type)
synth ctx = synthVar ctx
