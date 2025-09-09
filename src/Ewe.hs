{-# LANGUAGE GADTs, ApplicativeDo, DerivingVia, ImpredicativeTypes #-}
module Ewe where

import Control.Applicative
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Char as Char

data Parser t a where
  Pure :: a -> Parser t a
  Bind :: Parser t b -> (b -> Parser t a) -> Parser t a
  Alt :: Parser t a -> Parser t a -> Parser t a
  Is :: (t -> Bool) -> Parser t t
  Fail :: Parser t a
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
  Validate :: Parser t (b -> Either String a) -> Parser t (b -> Parser t a)

bind :: Parser t a -> (a -> Parser t b) -> Parser t b
bind (Pure a) k = k a
bind a k = Bind a k

instance Functor (Parser t) where
  fmap f a = bind a (\av -> Pure (f av))

instance Applicative (Parser t) where
  pure = Pure
  f <*> a = bind f (\fv -> bind a (\av -> Pure (fv av)))

instance Monad (Parser t) where
  a >>= f = bind a f

instance Alternative (Parser t) where
  empty = Fail
  (<|>) = Alt

acceptsTok :: Parser t a -> t -> Bool
acceptsTok (Pure _) _ = True
acceptsTok (Bind (Pure a) k) t = acceptsTok (k a) t
acceptsTok (Bind p _) t = acceptsTok p t
acceptsTok (Alt a b) t = acceptsTok a t || acceptsTok b t
acceptsTok (Is p) t = p t
acceptsTok (Fail) _ = False

parse :: Parser t a -> [t] -> Maybe (a, [t])
parse (Pure a) ts = Just (a, ts)
parse (Bind pb k) ts = do
  (bv, ts') <- parse pb ts
  parse (k bv) ts'
parse (Alt a b) (t : ts)
  | acceptsTok a t = parse a (t : ts)
  | otherwise = parse b (t : ts)
parse (Alt a b) [] = parse a [] <|> parse b []
parse (Is p) (t : ts)
  | p t = Just (t, ts)
  | otherwise = Nothing
parse (Is _) [] = Nothing
parse (Fail) _ = Nothing
parse (Validate p) ts = do
  (validator, ts') <- parse p ts
  Just
    ( \b ->
        case validator b of
          Left _ -> Fail
          Right a -> Pure a
    , ts'
    )

is :: (t -> Bool) -> Parser t t
is = Is

tok :: Eq t => t -> Parser t ()
tok t = is (== t) *> pure ()

whitespace :: Parser Char ()
whitespace = many (is Char.isSpace) *> pure ()

validate :: Parser t (b -> Either String a) -> Parser t (b -> Parser t a)
validate p = do
  validator <- p
  return \b ->
    case validator b of
      Left _ -> Fail
      Right a -> Pure a
