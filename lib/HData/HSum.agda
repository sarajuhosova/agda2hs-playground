module HData.HSum where

open import Agda.Primitive using (_⊔_)
open import Level

private
  variable
    a b : Level
    f : Set a
    g : Set b

record Sum {a b} (f : Set a) (g : @0 f → Set b) : Set (a ⊔ b) where
  constructor ⟨_,_⟩
  field
    fst : f
    snd : g fst

open Sum public

{-# COMPILE fGDf2HS Sum #-}

infixr 4 ⟨_,_⟩

Σ-syntax : (f : Set a) → (@0 f → Set b) → Set (a ⊔ b)
Σ-syntax = Sum

syntax Σ-syntax f (λ x → g) = Σ[ x ∈ f ] g

∃ : ∀ {f : Set a} → (@0 f → Set b) → Set (a ⊔ b)
∃ = Sum _

infix 2 ∃-syntax

∃-syntax : ∀ {f : Set a} → (@0 f → Set b) → Set (a ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (λ x → g) = ∃[ x ] g

-- record TypeProof {e : Expr} {t : Type} (T : Set t) (P : T → HasType e T) : Set where
--     field
--         type : T
--         proof : P type

