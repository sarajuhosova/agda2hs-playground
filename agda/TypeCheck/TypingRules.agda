module TypeCheck.TypingRules {@0 name : Set} where

open import TypeCheck.Context {name}
open import TypeCheck.Lang {name}
open import TypeCheck.Type
open import Util.Scope

private variable
  @0 x : name
  @0 α : Scope name
  a b : Type
  u v : Term α

data TyTerm (@0 Γ : Context α) : @0 Term α → @0 Type → Set 
  
infix 3 TyTerm
-- use \∶ to make the symbol
syntax TyTerm Γ u t = Γ ⊢ u ∶ t

data TyTerm {α} Γ where

  TyTVar
    : (p : x ∈ α)
    ----------------------------------
    → Γ ⊢ TVar x p ∶ lookupVar Γ x p

  TyLam
    : Γ , x ∶ a ⊢ u ∶ b
    -------------------------------
    → Γ ⊢ TLam x u ∶ TyArr a b

  TyApp
    : Γ ⊢ u ∶ (TyArr a b)
    → Γ ⊢ v ∶ a
    ------------------------------------
    → Γ ⊢ TApp u v ∶ b

{-# COMPILE AGDA2HS TyTerm deriving Show #-}
