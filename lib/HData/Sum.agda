module HData.Sum where

open import Agda.Primitive renaming (_⊔_ to _union_)
open import Level

private
  variable
    a b : Level
    f : Set a
    g : Set b

record Sum {a b} (f : Set a) (g : @0 f → Set b) : Set (a union b) where
  constructor _,_
  field
    fst : f
    snd : g fst

open Sum public

{-# COMPILE fGDf2HS Sum #-}
