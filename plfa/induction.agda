import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identity : ∀ (m : ℕ) → m + zero ≡ m
+-identity zero = begin zero + zero ≡⟨⟩ zero ∎ 
+-identity (suc m) =
    begin
        suc m + zero
    ≡⟨⟩
        suc ( m + zero )
    ≡⟨ cong suc (( +-identity m )) ⟩
        suc m
    ∎ 

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = begin zero + suc n ≡⟨⟩ suc ( zero + n ) ∎
+-suc (suc m) n =
    begin
        suc m + suc n
    ≡⟨⟩
        suc (m + suc n)
    ≡⟨ cong suc (+-suc m n) ⟩
        suc (suc m + n)
    ∎ 

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
    begin
        m + zero
    ≡⟨ +-identity m ⟩
        m
    ≡⟨⟩
        zero + m
    ∎
+-comm m (suc n) = 
    begin
        m + (suc n)
    ≡⟨ +-suc m n ⟩
        suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
        suc (n + m)
    ≡⟨⟩
        (suc n) + m
    ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc m n | +-comm m n = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p =
    begin
        zero + (n + p)
    ≡⟨ +-assoc zero n p ⟩
        (zero + n) + p
    ≡⟨ cong (_+ p ) (+-comm zero n) ⟩
        (n + zero) + p
    ≡⟨ +-assoc n zero p ⟩
        n + (zero + p)
    ∎
+-swap (suc m) n p = 
    begin
        (suc m) + (n + p)
    ≡⟨⟩
        suc (m + (n + p))
    ≡⟨ cong suc (+-swap m n p) ⟩
        suc (n + (m + p))
    ≡⟨ sym (+-suc n (m + p)) ⟩
        n + suc (m + p)
    ≡⟨⟩
        n + ((suc m) + p)
    ∎

+-swap′ : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap′ zero n p
    rewrite +-assoc zero n p
          | +-comm zero n
          | +-assoc n zero p
    = refl
+-swap′ (suc m) n p
    rewrite +-swap′ m n p
          | +-suc n (m + p)
    =  refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p =
    begin
        (zero + n) * p
    ≡⟨ cong (_* p) (+-comm zero n) ⟩
        (n + zero) * p
    ≡⟨ cong (_* p) (+-identity n) ⟩
        n * p
    ≡⟨⟩
        zero + n * p
    ≡⟨⟩ -- cong (_+ (n * p)) refl
        zero * p + n * p
    ∎
*-distrib-+ (suc m) n p =
    begin
        (suc m + n) * p
    ≡⟨⟩
        suc (m + n) * p
    ≡⟨⟩ -- (suc m) * n  =  n + (m * n)
        p + (m + n) * p
    ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
        p + (m * p + n * p)
    ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
        p + m * p + n * p
    ≡⟨⟩
        suc m * p + n * p
    ∎

*-distrib-+′ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+′ zero n p 
    rewrite +-comm zero n
          | +-identity n
    = refl
*-distrib-+′ (suc m) n p
    rewrite *-distrib-+ m n p
          | +-assoc p (m * p) (n * p)
    = refl
