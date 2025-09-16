module EweBnf where

{-
data Bnf env out =

data PrefixClause env out = PrefixClause String (Clause env out)

data Clause env out = Clause [Expr env out] (env -> Either String out)

data Expr env out
  = Terminal String
  | NonTerminal (Bnf env out)
  | Many (Prefix
-}
