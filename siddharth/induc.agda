import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)


+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p  = refl

+-identity : ∀ (m : ℕ) →  m + zero ≡ m
+-identity zero = refl
+-identity (suc m) rewrite +-identity m  = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero rewrite +-identity m = refl
+-comm m (suc n) rewrite +-suc′ m n | +-comm m n  = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite +-comm m (n + p) | +-assoc n p m | +-comm p m  = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | +-assoc p (m * p) (n * p) = refl

*-assoc : ∀ m n p → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl


*-identity : ∀ (m : ℕ) → m * zero ≡ zero
*-identity zero = refl
*-identity (suc m) rewrite *-identity m = refl

*-suc′ : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc′ zero n = refl
*-suc′ (suc m) n rewrite *-suc′ m n | +-swap n m (m * n) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero rewrite *-identity m  = refl
*-comm m (suc n) rewrite *-suc′ m n | *-comm m n = refl
