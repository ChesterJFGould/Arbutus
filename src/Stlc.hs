module Stlc where

import qualified Data.Char as Char
import Data.String
import Control.Applicative
import Ewe

data Var = MkVar String
  deriving (Eq, Show)

instance IsString Var where
  fromString = MkVar

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

varChar :: Parser l Char Char
varChar = is Char.isLetter

var :: Parser l Char Var
var = MkVar <$> some varChar

parens :: Parser l Char a -> Parser l Char a
parens p = tok '(' *> whitespace *> p <* whitespace <* tok ')'

checkSynthValidator :: (Ctx Type -> Validator l (Type, Expr)) -> Ctx Type -> Type -> Validator l Expr
checkSynthValidator s ctx t =
  handle $ fmap
    (\(t', e) ->
      case t == t' of
        True -> Right e
        False -> Left (concat ["Expected a `", show t, "` but got a `", show t', "`"])
    )
    (s ctx)

checkSynth :: Parser l Char (Ctx Type -> Type -> Validator l Expr)
checkSynth = checkSynthValidator <$> varSynth

check :: Parser l Char (Ctx Type -> Type -> Validator l Expr)
check = checkSynth

funValidation :: (Ctx Type -> Validator l (Type, Expr)) -> Ctx Type -> Validator l (Type, Type, Expr)
funValidation fv ctx =
  handle $ fmap
    (\(t, f) ->
      case t of
        Fun domain codomain -> Right (domain, codomain, f)
        _ -> Left (concat ["Expected a function, but is of type `", show t, "`"])
    )
    (fv ctx)

appValidator :: (Ctx Type -> Validator l (Type, Type, Expr)) -> (Ctx Type -> Type -> Validator l Expr) -> Ctx Type -> Validator l (Type, Expr)
appValidator fv argv ctx =
  validatorBind
    (fv ctx)
    ( \(domain, codomain, f) ->
        (\arg -> (codomain, App f arg)) <$> (argv ctx domain)
    )

app :: Parser l Char (Ctx Type -> Validator l (Type, Expr))
app =
  appValidator
    <$> ((funValidation <$> varSynth) <* whitespace)
    <*> parens check

varValidation :: Validator l Var -> Ctx Type -> Validator l (Type, Expr)
varValidation v ctx =
  handle $ fmap
    (\x ->
      case lookupCtx x ctx of
        Nothing -> Left (concat ["Unbound variable `", show x, "`"])
        Just t -> Right (t, Var x)
    )
    v

varSynth :: Parser l Char (Ctx Type -> Validator l (Type, Expr))
varSynth = varValidation <$> startValidation var

synth :: Parser l Char (Ctx Type -> Validator l (Type, Expr))
synth = app <|> varSynth <|> parens synth

topValidator :: Ctx Type -> (Ctx Type -> Validator l (Type, Expr)) -> Validator l (Type, Expr)
topValidator ctx s = s ctx

top :: Ctx Type -> Parser l Char (Type, Expr)
top ctx = validate $ topValidator ctx <$> app
