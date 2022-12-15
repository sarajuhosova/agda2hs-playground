module Tree.Tree where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl; cong; sym)
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

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

addSingleElement : (e : Int) → (flatten (add e Nil) == (e ∷ [])) ≡ True
addSingleElement e =
    begin
        flatten (add e Nil) == (e ∷ [])
    ≡⟨⟩
        flatten (Tree e Nil Nil) == (e ∷ [])
    ≡⟨⟩
        flatten Nil ++ (e ∷ []) ++ flatten Nil == (e ∷ [])
    ≡⟨⟩
        [] ++ (e ∷ []) ++ [] == (e ∷ [])
    ≡⟨⟩
        (e ∷ []) == (e ∷ [])
    ≡⟨ {!   !} ⟩
        e == e
    ≡⟨⟩
        eqInt e e
    ≡⟨ {!   !} ⟩
        True
    ∎

 