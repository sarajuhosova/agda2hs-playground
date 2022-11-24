import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_;  _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

seven : ℕ
seven = suc ( suc ( suc ( suc ( suc ( suc ( suc ( zero ) ) ) ) ) ) )

-- ADDITION -------------------------------------------------

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
    begin
        2 + 3
    ≡⟨⟩
        suc ( suc ( zero ) ) + suc ( suc ( suc ( zero ) ) )
    ≡⟨⟩
        suc ( suc ( zero ) + suc ( suc ( suc ( zero ) ) ) )
    ≡⟨⟩
        suc ( suc ( zero + suc ( suc ( suc ( zero ) ) ) ) )
    ≡⟨⟩
        suc ( suc ( suc ( suc ( suc ( zero ) ) ) ) )
    ≡⟨⟩
        5
    ∎

_ : 2 + 3 ≡ 5
_ = refl

_ : 3 + 4 ≡ 7
_ =
    begin
        3 + 4
    ≡⟨⟩
        suc ( 2 + 4 )
    ≡⟨⟩
        suc ( suc ( 1 + 4 ) )
    ≡⟨⟩
        suc ( suc ( suc ( 0 + 4 ) ) )
    ≡⟨⟩
        suc ( suc ( suc ( 4 ) ) )
    ≡⟨⟩
        7
    ∎

-- MULTIPLICATION -------------------------------------------

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

_^_ : ℕ → ℕ → ℕ
m ^ zero     =  1
m ^ (suc n)  =  m * (m ^ n)

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

infixl 6  _+_  _∸_
infixl 7  _*_

-- BINARY NUMBERS -------------------------------------------

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

eleven : Bin
eleven = ⟨⟩ O O I O I I

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = inc b O

_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ = 
    begin
        inc (⟨⟩ I I)
    ≡⟨⟩
        inc ( ⟨⟩ I ) O
    ≡⟨⟩
        inc ⟨⟩ O O
    ≡⟨⟩
        ⟨⟩ I O O
    ∎

to   : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc ( to ( n ) )

from : Bin → ℕ
from ⟨⟩ = zero
from (b O) = from b * 2
from (b I) = suc ( from b * 2 )

_ : from (⟨⟩ O) ≡ zero
_ =
    begin
        from (⟨⟩ O)
    ≡⟨⟩
        (from ⟨⟩) * 2
    ≡⟨⟩
        zero * 2
    ≡⟨⟩
        zero
    ∎

_ : ⟨⟩ O ≡ to ( zero )
_ = 
    begin
        ⟨⟩ O
    ≡⟨⟩
        to ( zero )
    ∎

_ : from (⟨⟩ I) ≡ suc ( zero )
_ = refl

_ : ⟨⟩ I ≡ to ( suc ( zero ) )
_ = refl

_ : from (⟨⟩ I O) ≡ suc ( suc ( zero ) )
_ = refl

_ : ⟨⟩ I O ≡ to ( suc ( suc ( zero ) ) )
_ = refl

_ : from (⟨⟩ I I) ≡ 3
_ = refl

_ : ⟨⟩ I I ≡ to ( 3 )
_ = refl

_ : from (⟨⟩ I O O) ≡ 4
_ = 
    begin
        from (⟨⟩ I O O)
    ≡⟨⟩
        (from ( ⟨⟩ I O )) * 2
    ≡⟨⟩
        ( from ( ⟨⟩ I ) * 2 ) * 2
    ≡⟨⟩
        ( suc ( from ⟨⟩ * 2 ) * 2 ) * 2
    ≡⟨⟩
        ( suc ( zero * 2 ) * 2 ) * 2
    ≡⟨⟩
        ( suc zero * 2 ) * 2
    ≡⟨⟩
        ( 1 * 2 ) * 2
    ≡⟨⟩
        2 * 2
    ≡⟨⟩
        4
    ∎

_ : ⟨⟩ I O O ≡ to ( 4 )
_ = 
    begin
        ⟨⟩ I O O
    ≡⟨⟩
        inc ( ⟨⟩ I I )
    ≡⟨⟩
        inc ( inc ( ⟨⟩ I O ) )
    ≡⟨⟩
        inc ( inc ( inc ( ⟨⟩ I ) ) )
    ≡⟨⟩
        inc ( inc ( inc ( inc ( ⟨⟩ O ) ) ) )
    ≡⟨⟩
        inc ( inc ( inc ( inc ( to ( zero ) ) ) ) )
    ≡⟨⟩
        inc ( inc ( inc ( to ( 1 ) ) ) )
    ≡⟨⟩
        inc ( inc ( to ( 2 ) ) )
    ≡⟨⟩
        inc ( to ( 3 ) )
    ≡⟨⟩
        to ( 4 )
    ∎
