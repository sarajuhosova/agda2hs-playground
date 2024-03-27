module Interp.Grammar where

open import Haskell.Prelude

data Type : Set where
    TNat  : Type
    TBool : Type
    TProd : Type → Type → Type
    TFun  : Type → Type → Type

{-# COMPILE AGDA2HS Type #-}

data Expr : {@0 t : Type} → Set where
    ENat  : Nat → Expr {TNat}
    EBool : Bool → Expr {TBool}
    ESum  : {l r : Type} → Expr {l} → Expr {r} → Expr {TProd l r}
    ELam  : {b : Type} → String → (x : Type) → Expr {b} → Expr {TFun x b}
    EApp  : {x b : Type} → Expr {TFun x b} → Expr {x} → Expr {b}

{-# COMPILE AGDA2HS Expr #-}
