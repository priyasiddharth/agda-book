module scott.Matrices where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

-- Simple 2x2 matrix definition.
data 𝕄2x2 : Set where
    m2x2 : ℕ → ℕ → ℕ → ℕ → 𝕄2x2

-- Matrix multiplication by definition.
_*ᴹ_ : 𝕄2x2 → 𝕄2x2 → 𝕄2x2
(m2x2 x11 x12 x21 x22) *ᴹ (m2x2 y11 y12 y21 y22) = (m2x2 (x11 * y11 + x12 * y21) (x11 * y12 + x12 * y22) (x21 * y11 + x22 * y21) (x21 * y12 + x22 * y22))

-- Projections to relate elements of one matrix to elements of another.
-- This simplifies proofs.
proj1ᴹ : 𝕄2x2 → ℕ → 𝕄2x2
proj2ᴹ : 𝕄2x2 → ℕ → 𝕄2x2
proj3ᴹ : 𝕄2x2 → ℕ → 𝕄2x2
proj4ᴹ : 𝕄2x2 → ℕ → 𝕄2x2
proj1ᴹ (m2x2 a b c d) n = (m2x2 n b c d)
proj2ᴹ (m2x2 a b c d) n = (m2x2 a n c d)
proj3ᴹ (m2x2 a b c d) n = (m2x2 a b n d)
proj4ᴹ (m2x2 a b c d) n = (m2x2 a b c n)

-- (Lemma 1) 1 * m ≡ m
-- "One is a multiplicative identity".
*-identityʳ : ∀ (m : ℕ) → 1 * m ≡ m
*-identityʳ m  rewrite +-comm m 0 = refl

-- (Lemma 2) (m2x2 (1 * a) (1 * b) (1 * c) (1 * d)) ≡ (m2x2 a b c d)
-- "One is the scalar identity of a matrix".
m2x2-scale-by-1 : ∀ (a b c d : ℕ) → (m2x2 (1 * a) (1 * b) (1 * c) (1 * d)) ≡ (m2x2 a b c d)
m2x2-scale-by-1 a b c d =
  begin
    (m2x2 (1 * a) (1 * b) (1 * c) (1 * d))
  ≡⟨ cong (proj1ᴹ (m2x2 (1 * a) (1 * b) (1 * c) (1 * d))) (*-identityʳ a) ⟩
    (m2x2 a (1 * b) (1 * c) (1 * d))
  ≡⟨ cong (proj2ᴹ (m2x2 a (1 * b) (1 * c) (1 * d))) (*-identityʳ b) ⟩
    (m2x2 a b (1 * c) (1 * d))
  ≡⟨ cong (proj3ᴹ (m2x2 a b (1 * c) (1 * d))) (*-identityʳ c) ⟩
    (m2x2 a b c (1 * d))
  ≡⟨ cong (proj4ᴹ (m2x2 a b c (1 * d)))  (*-identityʳ d) ⟩
    (m2x2 a b c d)
  ∎

-- Proof.
m2x2_inverse_a : ∀ (m : 𝕄2x2) → (m2x2 1 0 0 1) *ᴹ m ≡ m
m2x2_inverse_a (m2x2 y11 y12 y21 y22) =
  begin
    (m2x2 1 0 0 1) *ᴹ (m2x2 y11 y12 y21 y22)
  ≡⟨⟩
    (m2x2 (1 * y11 + 0 * y21) (1 * y12 + 0 * y22) (0 * y11 + 1 * y21) (0 * y12 + 1 * y22))
  ≡⟨⟩
    (m2x2 (1 * y11 + 0) (1 * y12 + 0) (0 + 1 * y21) (0 + 1 * y22))
  ≡⟨⟩
    (m2x2 (1 * y11 + 0) (1 * y12 + 0) (1 * y21) (1 * y22))
  ≡⟨ cong (proj1ᴹ (m2x2 (1 * y11 + 0) (1 * y12 + 0) (1 * y21) (1 * y22))) (*-identityʳ (1 * y11)) ⟩
    (m2x2 (1 * y11) (1 * y12 + 0) (1 * y21) (1 * y22))
  ≡⟨ cong (proj2ᴹ (m2x2 (1 * y11) (1 * y12 + 0) (1 * y21) (1 * y22))) (*-identityʳ (1 * y12)) ⟩
    (m2x2 (1 * y11) (1 * y12) (1 * y21) (1 * y22))
  ≡⟨ m2x2-scale-by-1 y11 y12 y21 y22 ⟩
    (m2x2 y11 y12 y21 y22)
  ∎
