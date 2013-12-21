module TypeTheory1 where

infixr 9 :*:
infixr 8 :+:
infixr 7 :->:
data Type = One | Zero | Type :*: Type | Type :+: Type | Type :->: Type
  deriving (Show,Eq)

type Name = String

infixl 6 :@:
data Context = Empty | Context :@: (Name, Type)
  deriving (Show,Eq)

contains :: Context -> Name -> Bool
contains Empty         _  = False
contains (g :@: (n,_)) n' = n == n' || contains g n'

data Term = Var Name
          -- One
          | Unit
          -- Zero
          | Abort Term
          -- :*:
          | Pair Term Term
          | Fst Term | Snd Term
          -- :+:
          | Inl Term | Inr Term
          | Case Term Name Term Name Term
          -- :->:
          | Lam Name Term
          | App Term Term
  deriving (Eq,Show)

infix 6 :::
data Judgment = CTX Context
              | Term ::: Type
  deriving (Eq,Show)

prove :: Context -> Judgment -> Bool
prove g (CTX Empty)          = True
prove g (CTX (g' :@: (n,_))) = not (g' `contains` n)
                            && prove g (CTX g')
prove Empty           (Var n ::: t) = False
prove (g :@: (n',t')) (Var n ::: t) = if n' == n
                                      then t' == t
                                      else prove g (Var n ::: t)
prove g (Unit ::: One) = True
prove g (Abort m ::: c) = prove g (m ::: Zero)
prove g (Pair m n ::: a :*: b) = prove g (m ::: a) && prove g (n ::: b)
prove g (Fst p ::: a)          = prove g (p ::: a :*: undefined)
prove g (Snd p ::: b)          = prove g (p ::: undefined :*: b)
prove g (Inl m ::: a :+: b) = prove g (m ::: a)
prove g (Inr n ::: a :+: b) = prove g (n ::: b)
prove g (Case d x m y n ::: c) = prove g (d ::: undefined :+: undefined)
                              && prove (g :@: (x,undefined)) (m ::: undefined)
                              && prove (g :@: (y,undefined)) (n ::: undefined)
prove g (Lam x m ::: a :->: b) = prove (g :@: (x, a)) (m ::: b)
prove g (App f m ::: b)        = prove g (f ::: undefined :->: b)
                              && prove g (m ::: undefined)
