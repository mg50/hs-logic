
module Constraint (
  notEq,
  (=/=)
) where
import HLogic

notEqConstraint :: (Termable a, Termable b) => a -> b -> Constraint
notEqConstraint x y bin = case (toTerm x, toTerm y) of
  (TVar a, TVar b) -> deepLookup (LVar a) bin /= deepLookup (LVar b) bin
  (TVar a, b) -> deepLookup (LVar a) bin /= b
  (b, TVar a) -> deepLookup (LVar a) bin /= b
  (a,b) -> a /= b

notEq :: (Termable a, Termable b) => a -> b -> Predicate
notEq a b = MLogic $ \s@(Substitution bin count cons) ->
  case unify (toTerm a) (toTerm b) s of
    Zonk -> [(s, ())]
    s' | (bindings s') == (bindings s) -> []
    _ -> let newConstraint = notEqConstraint (toTerm a) (toTerm b)
             s' = s{constraints = (newConstraint:cons)}
         in [(s', ())]

(=/=) :: (Termable a, Termable b) => a -> b -> Predicate
(=/=) = notEq

genCompConstraint :: (Termable a, Termable b) =>
                      (Int -> Int -> Bool) -> a -> b -> Constraint
genCompConstraint op x y b = case (sortaDeepLookup x' b, sortaDeepLookup y' b) of
  (TInt a, TInt b) -> a `op` b
  (TVar _, TInt _) -> True
  (TInt _, TVar _) -> True
  _                -> False
  where x' = toTerm x
        y' = toTerm y

genCompPredicate :: (Termable a, Termable b) =>
                     (Int -> Int -> Bool) -> a -> b -> Predicate
genCompPredicate op x y = MLogic $ \s@(Substitution _ _ cons) ->
    let newConstraint = genCompConstraint op x y
        s' = s{constraints = (newConstraint:cons)}
    in [(s', ())]

(?>=) :: (Termable a, Termable b) => a -> b -> Predicate
(?>=) = genCompPredicate (>=)

(?>) :: (Termable a, Termable b) => a -> b -> Predicate
(?>) = genCompPredicate (>)

(?<=) :: (Termable a, Termable b) => a -> b -> Predicate
(?<=) = genCompPredicate (<=)

(?<) :: (Termable a, Termable b) => a -> b -> Predicate
(?<) = genCompPredicate (<)

blah = run $ do
  x <- fresh
  membero x ([1, 2, 3] :: [Int])
  x ?>= (2 :: Int)
  x ?< (3 :: Int)
--  x =/= (2 :: Int)
  return x
