import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
module ind where
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

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

*-zeroʳ : ∀ (m : ℕ) → m * zero ≡ 0
*-zeroʳ zero = refl
*-zeroʳ (suc m) rewrite *-zeroʳ m = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero rewrite (+-identityʳ m) = refl
+-comm m (suc n) rewrite (+-suc m n) | (+-comm m n)  = refl

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q rewrite (+-assoc m n (p + q)) | (sym (+-assoc n p q)) | (+-assoc m (n + p) q) = refl

+-swap : ∀ (m n p :  ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite (sym (+-assoc m n p)) | +-comm m n | +-assoc n m p = refl

*-suc : ∀ (m n : ℕ) → n * suc m ≡ n + n * m
*-suc m zero = refl
*-suc m (suc n) rewrite *-suc m n | +-swap m n (n * m)= refl

*-comm : ∀ ( m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-zeroʳ n = refl
*-comm (suc m) n rewrite *-comm m n | sym (*-suc m n) = refl

*-dist-+ : ∀ (m n p : ℕ) → m * (n + p) ≡ (m * n) + (m * p)
*-dist-+ zero n p = refl
*-dist-+ (suc m) n p rewrite *-dist-+ m n p | +-assoc n p (m * n + m * p) | +-swap p (m * n) (m * p) | sym (+-assoc n (m * n) (p + (m * p)))  = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-comm (n + m * n) p | *-dist-+ p n (m * n) | *-comm n p | sym (*-assoc p m n) | *-comm p m | *-assoc m p n = refl

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p rewrite +-identityʳ (m ^ p) = refl
^-distribˡ-+-* m (suc n) p rewrite ^-distribˡ-+-* m n p | sym (*-assoc m (m ^ n) (m ^ p)) = refl

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) rewrite ^-distribʳ-* m n p | *-assoc m n ((m ^ p) * (n ^ p)) | sym (*-assoc n (m ^ p) (n ^ p))  | *-comm n (m ^ p) | *-assoc (m ^ p) n (n ^ p) | *-assoc m (m ^ p) (n * (n ^ p)) = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero rewrite *-zeroʳ n = refl
^-*-assoc m n (suc p) rewrite ^-*-assoc m n p | sym (^-distribˡ-+-* m n (n * p)) | sym (*-suc p n) = refl

