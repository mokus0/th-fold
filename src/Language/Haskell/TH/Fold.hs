{-
 -  ``Util/TH/Fold''
 -  First attempt at a generic catamorphism...
 -}

-- |This is \"very old\" code and I'd like to clean it up, but it more or less
--  works so it's a pretty low priority right now.
--
-- My apologies for inflicting this code upon the world ( ;-) ), but I
-- did not see anything else \"out there\", so I figured I'd provide
-- a seed crystal around which something better might form.

module Language.Haskell.TH.Fold (fold) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Control.Monad

replaceAt :: Integral a => a -> b -> [b] -> [b]
replaceAt _ _ []     = []
replaceAt 0 y (_:xs) = y : xs
replaceAt (n+1) y (x:xs) = x : replaceAt n y xs

arity :: (Num a) => Type -> a
arity (ForallT _ _ t)       = arity t
arity (AppT (AppT ArrowT _) t)  = 1 + arity t
arity _             = 0

conName :: Con -> Name
conName (NormalC name _)    = name
conName (RecC    name _)    = name
conName (InfixC _ name _)   = name
conName (ForallC _ _ con)   = conName con

conArity :: (Num a) => Name -> Q a
conArity con = do
    DataConI _ conType _ _ <- reify con
    return (arity conType)

conArgTypes :: Con -> [Type]
conArgTypes (NormalC _ args)    = map snd args
conArgTypes (RecC    _ args)    = map (\(_,_,ty) -> ty) args
conArgTypes (InfixC t1 _ t2)    = [snd t1, snd t2]
conArgTypes (ForallC _ _ con)   = conArgTypes con

typeCons :: Name -> Q [Con]
typeCons ty = do
    TyConI (typeDec) <- reify ty
    return (typeDecDataCons typeDec)

typeDecDataCons :: Dec -> [Con]
typeDecDataCons (DataD _ _ _ cons _)    = cons
typeDecDataCons (NewtypeD _ _ _ con _)  = [con]
typeDecDataCons (TySynD _ _ ty)     = error "typeDecDataCons doesn't support type synonyms"
typeDecDataCons _           = error "typeDecDataCons: not a type"

foldClause :: ExpQ -> Name -> [Name] -> Int -> Con -> Int -> ClauseQ
foldClause self ty funcNames nCons con conN = do
    let cName = conName con
    conArity <- conArity cName
    
    let funcName = funcNames !! conN
    let funcE = varE funcName
    
    conArgs <- replicateM conArity (newName "x")
    let conArgsPs = map varP conArgs
    let conArgsEs = map varE conArgs
    let conArgP = conP cName conArgsPs
    
    let addRecursion argType argE = case argType of
            ConT x
                | x == ty   -> appE self argE
            AppT (ConT x) _ 
                | x == ty   -> appE self argE
            -- probably wrong; should check applied-to type for equality
            -- with type parameter?
            AppT (AppT (ConT x) _) _ 
                | x == ty   -> appE self argE
            _           -> argE
    let argTypes = conArgTypes con
    let conArgsEsWithRecursion = zipWith addRecursion argTypes conArgsEs
    
    let funArgsPs = map varP funcNames
    
    let pats = funArgsPs ++ [conArgP]
    let body = normalB (appsE (funcE : conArgsEsWithRecursion) )
    clause pats body []

foldDec :: Name -> ExpQ -> Name -> [Name] -> [Con] -> DecQ
foldDec fName self ty funcNames cons = funD fName clauses
    where
        nCons = length cons
        clauses = zipWith (foldClause self ty funcNames nCons) cons [0..]

-- |Generate a very basic fold operation given the 'Name' of a type
-- constructor.  Data constructors of the specified type become function
-- parameters to the fold, in the same order the type defines them.  Simple
-- recursive references in the type's constructors become recursive calls to
-- the fold.
-- 
-- At present this only properly handles very simple types.
-- Basically, that means types that have no parameters, types with one parameter
-- where the only recursion is via field slots with types of the form 'T a'
-- where 'a' is the type of the parameter, and more complicated types without
-- recursion.
fold :: Name -> ExpQ
fold ty = do
    cons <- typeCons ty
    fName <- newName "fold"
    let fE = varE fName
    
    let nCons = length cons
    funcNames <- replicateM nCons (newName "f")
    
    let self = appsE (fE : map varE funcNames)
    
    let fn = foldDec fName self ty funcNames cons
    letE [fn] fE
