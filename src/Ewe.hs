{-# LANGUAGE GADTs, ApplicativeDo, DerivingVia #-}
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
  Validate :: Parser t (Either String a) -> Parser t a

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
parse (Validate a) ts = do
  (aOrErr, ts') <- parse a ts
  case aOrErr of
    Left _ -> Nothing
    Right a -> Just (a, ts')

is :: (t -> Bool) -> Parser t t
is = Is

tok :: Eq t => t -> Parser t ()
tok t = is (== t) *> pure ()

whitespace :: Parser Char ()
whitespace = many (is Char.isSpace) *> pure ()

validate :: Parser t (Either String a) -> Parser t a
validate = Validate
