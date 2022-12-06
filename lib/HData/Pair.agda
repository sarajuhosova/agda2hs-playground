module HData.Pair where

record DepPair (a b : Set) : Set where
    field
        fst : a
        snd : b

open DepPair public

{-# COMPILE AGDA2HS DepPair #-}
