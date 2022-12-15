module Tree.Tree where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl; cong; sym)
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Agda.Builtin.Word

-- DATA DEFINITION ----------------------------------------

data SearchTree : Set where
    Nil : SearchTree
    Tree : Int → SearchTree → SearchTree → SearchTree

eqSearchTree : SearchTree → SearchTree → Bool
eqSearchTree Nil Nil = True
eqSearchTree (Tree e1 l1 r1) (Tree e2 l2 r2) = e1 == e2 && eqSearchTree l1 l2 && eqSearchTree r1 r2
eqSearchTree _ _ = False

instance
  iEqSearchTree : Eq SearchTree
  iEqSearchTree ._==_ = eqSearchTree

{-# COMPILE AGDA2HS SearchTree #-}
{-# COMPILE AGDA2HS eqSearchTree #-}
{-# COMPILE AGDA2HS iEqSearchTree #-}

-- METHODS ------------------------------------------------

add : Int → SearchTree → SearchTree
add i Nil = Tree i Nil Nil
add i (Tree e left right) = if i < e then Tree e (add i left) right else Tree e left (add i right)

{-# COMPILE AGDA2HS add #-}

addAll : List Int → SearchTree → SearchTree
addAll xs tree = foldl ((λ t x → add x t)) tree xs

{-# COMPILE AGDA2HS addAll #-}

flatten : SearchTree → List Int
flatten Nil = []
flatten (Tree e left right) = flatten left ++ (e ∷ []) ++ flatten right

{-# COMPILE AGDA2HS flatten #-}

-- PROOFS -------------------------------------------------

≡-eqNat : ∀ (left right : Nat) → (left == right) ≡ True → left ≡ right
≡-eqNat zero zero h = refl
≡-eqNat (suc left) (suc right) h
    rewrite ≡-eqNat left right h
    = refl

≡-Nat-≡-eqInt : ∀ (left right : Word64) 
                → (primWord64ToNat left == primWord64ToNat right) ≡ True 
                → (int64 left) ≡ (int64 right)
≡-Nat-≡-eqInt i j h = {!  !}

≡-eqInt : ∀ (left right : Int) → (left == right) ≡ True → left ≡ right
≡-eqInt (int64 i) (int64 j) h = ≡-Nat-≡-eqInt i j h

&&-left-assoc : ∀ (a b c : Bool) → (a && b && c) ≡ True → ((a && b) && c) ≡ True
&&-left-assoc True True True h = refl

&&-leftTrue : ∀ (a b : Bool) → (a && b) ≡ True → a ≡ True
&&-leftTrue True True h = refl

&&-rightTrue : ∀ (a b : Bool) → (a && b) ≡ True → b ≡ True
&&-rightTrue True True h = refl

eq : ∀ (left right : SearchTree) → (left == right) ≡ True → left ≡ right
eq Nil Nil h = refl
eq Nil (Tree x right right₁) ()
eq (Tree x₁ left₁ right₁) (Tree x₂ left₂ right₂) h
    rewrite ≡-eqInt x₁ x₂ (&&-leftTrue
                (eqInt x₁ x₂)
                (eqSearchTree left₁ left₂)
                (&&-leftTrue
                    (eqInt x₁ x₂ && eqSearchTree left₁ left₂)
                    (eqSearchTree right₁ right₂)
                    (&&-left-assoc
                        (eqInt x₁ x₂)
                        (eqSearchTree left₁ left₂)
                        (eqSearchTree right₁ right₂)
                        h
                    )
                )
            )
            | eq left₁ left₂ (&&-rightTrue
                (eqInt x₁ x₂)
                (eqSearchTree left₁ left₂)
                (&&-leftTrue
                    (eqInt x₁ x₂ && eqSearchTree left₁ left₂)
                    (eqSearchTree right₁ right₂)
                    (&&-left-assoc
                        (eqInt x₁ x₂)
                        (eqSearchTree left₁ left₂)
                        (eqSearchTree right₁ right₂)
                        h
                    )
                )
            )
            | eq right₁ right₂ (&&-rightTrue 
                (eqInt x₁ x₂ && eqSearchTree left₁ left₂)
                (eqSearchTree right₁ right₂)
                (&&-left-assoc
                    (eqInt x₁ x₂)
                    (eqSearchTree left₁ left₂)
                    (eqSearchTree right₁ right₂)
                    h
                )
            )
    = refl

addSingleElement : (e : Int) → flatten (add e Nil) ≡ e ∷ []
addSingleElement e = refl
    -- begin
    --     flatten (add e Nil)
    -- ≡⟨⟩
    --     flatten (Tree e Nil Nil)
    -- ≡⟨⟩
    --     flatten Nil ++ (e ∷ []) ++ flatten Nil
    -- ≡⟨⟩
    --     [] ++ (e ∷ []) ++ []
    -- ≡⟨⟩
    --     e ∷ []
    -- ∎

-- addSingleElement : (e : Int) → (flatten (add e Nil) == (e ∷ [])) ≡ True
-- addSingleElement e =
--     begin
--         flatten (add e Nil) == (e ∷ [])
--     ≡⟨⟩
--         flatten (Tree e Nil Nil) == (e ∷ [])
--     ≡⟨⟩
--         flatten Nil ++ (e ∷ []) ++ flatten Nil == (e ∷ [])
--     ≡⟨⟩
--         [] ++ (e ∷ []) ++ [] == (e ∷ [])
--     ≡⟨⟩
--         e ∷ [] == e ∷ []
--     ≡⟨ sym {!   !} ⟩
--         e == e
--     ≡⟨⟩
--         eqInt e e
--     ≡⟨ {!   !} ⟩
--         True
--     ∎

  