{-# LANGUAGE NoMonomorphismRestriction #-}
module Constraint (
  notEq,
  (=/=)
) where
import HLogic
import Control.Monad hiding (fail)
import Debug.Trace
import qualified Data.Map as Map

confirm :: Substitution -> Bool -> Substitution
confirm sub bool = if bool then sub else Failure

notEqConstraint :: (Termable a, Termable b) => a -> b -> Constraint
notEqConstraint x y sub = confirm sub $ case (toTerm x, toTerm y) of
  (TVar a, TVar b) -> deepLookup (LVar a) bin /= deepLookup (LVar b) bin
  (TVar a, b) -> deepLookup (LVar a) bin /= b
  (b, TVar a) -> deepLookup (LVar a) bin /= b
  (a,b) -> a /= b
  where bin = bindings sub

notEq :: (Termable a, Termable b) => a -> b -> Predicate
notEq a b = MLogic $ \s@(Substitution bin count cons) ->
  case unify (toTerm a) (toTerm b) s of
    Failure -> [(s, ())]
    s' | (bindings s') == (bindings s) -> []
    _ -> let newConstraint = notEqConstraint (toTerm a) (toTerm b)
             s' = s{constraints = newConstraint:cons}
         in [(s', ())]

(=/=) :: (Termable a, Termable b) => a -> b -> Predicate
(=/=) = notEq


genCompConstraint :: (Termable a, Termable b) =>
                     (Int -> Int -> Bool) -> a -> b -> Constraint
genCompConstraint op x y sub = confirm sub $ case (open x, open y) of
  (TInt a, TInt b) -> a `op` b
  (TVar _, TInt _) -> True
  (TInt _, TVar _) -> True
  _                -> False
  where open x = sortaDeepLookup (toTerm x) (bindings sub)

genCompPredicate :: (Termable a, Termable b) =>
                    (Int -> Int -> Bool) -> a -> b -> Predicate
genCompPredicate op x y = MLogic $ \s@(Substitution bindings _ cons) ->
    let newConstraint = genCompConstraint op x y
        s' = s{constraints = (newConstraint:cons)}
    in case newConstraint s of
      Failure -> []
      _    -> [(s', ())]

(?>=) = genCompPredicate (>=)
(?>) = genCompPredicate (>)
(?<=) = genCompPredicate (<=)
(?<) = genCompPredicate (<)


fromTInt :: Term -> Int
fromTInt (TInt x) = x
fromTInt _ = error "cannot convert from TInt"

couldBeTInt :: Term -> Bool
couldBeTInt (TInt _) = True
couldBeTInt (TVar _) = True
couldBeTInt _ = False

genBinopConstraint :: (Termable a, Termable b, Termable c) =>
                      (Int -> Int -> Int) ->
                      (Int -> Int -> Int) -> a -> b -> c -> Constraint
genBinopConstraint op inv x y z sub = case (open x, open y, open z) of
  ((TInt x), (TInt y), (TInt z)) | x `op` y == z -> sub
  ((TInt x), (TInt y), (TVar z)) -> unify (TVar z) (TInt $ x `op` y) sub
  ((TInt x), (TVar y), (TInt z)) -> go x z y sub
  ((TVar x), (TInt y), (TInt z)) -> go y z x sub
  (x, y, z) | all couldBeTInt [x, y, z] -> sub
  _ -> Failure
  where go x y z sub = unify (TVar z) (TInt $ x `inv` y) sub
        open x = sortaDeepLookup (toTerm x) (bindings sub)

genBinopPredicate :: (Termable a, Termable b, Termable c) =>
                     (Int -> Int -> Int) ->
                     (Int -> Int -> Int) -> a -> b -> c -> Predicate
genBinopPredicate op inv x y z = MLogic $ \s@(Substitution _ _ cons) ->
    let newConstraint = genBinopConstraint op inv x y z
        s' = s{constraints = (newConstraint:cons)}
        s'' = newConstraint s'
    in case s'' of
      Failure -> []
      _       -> [(s'', ())]

pluso = genBinopPredicate (+) (-)
minuso = genBinopPredicate (-) (+)
timeso = genBinopPredicate (*) div

sumo :: (Termable a, Termable b) => a -> b -> Predicate
sumo xs num = conda [[baseCase], [inductiveCase]]
  where baseCase = do xs === TNil
                      num === (0 :: Int)
        inductiveCase = do h <- fresh
                           t <- fresh
                           conso h t xs

                           tNum <- fresh
                           sumo t tNum
                           pluso h tNum num

dbg :: Term -> Predicate
dbg term = do s <- getEnv
              let val = sortaDeepLookup term (bindings s)
              ("debug: " ++ show val ++ "\n\n") `trace` return ()

lengtho :: (Termable a, Termable b) => a -> b -> Predicate
lengtho xs l = conda [[baseCase], [inductiveCase]]
  where baseCase = do xs === TNil
                      l === (0 :: Int)
        inductiveCase = do h <- fresh
                           t <- fresh
                           conso h t xs

                           l' <- fresh
                           lengtho t l'
                           pluso l' (1 :: Int) l
