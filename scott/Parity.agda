module scott.Parity where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

-- Definition of even and odd.
data even : ℕ → Set
data odd  : ℕ → Set

data even where
  evenzero : even zero
  evensuc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  oddsuc : ∀ {n : ℕ} → even n → odd (suc n)

-- A structure which holds of each natural number if it is even or odd.
data parity : ℕ → Set where
  peven : ∀ {n : ℕ} → even n → parity n
  podd  : ∀ {n : ℕ} → odd  n → parity n

parity-is-total : ∀ (n : ℕ) → parity n
parity-is-total zero               = peven evenzero
parity-is-total (suc n) with parity-is-total n
...                     | peven en = podd (oddsuc en)
...                     | podd  on = peven (evensuc on)

-- A data structure which holds true if two numbers share the same parity.
data same-parity : ℕ → ℕ → Set where
  seven : ∀ {m n : ℕ} → even m → even n → same-parity m n
  sodd  : ∀ {m n : ℕ} → odd  m → odd  n → same-parity m n

same-parity-is-reflexive : ∀ (n : ℕ) → same-parity n n
same-parity-is-reflexive zero                  = seven evenzero evenzero
same-parity-is-reflexive (suc n) with same-parity-is-reflexive n
...                              | seven em en = sodd (oddsuc em) (oddsuc en)
...                              | sodd om on  = seven (evensuc om) (evensuc on)

-- I'm still struggling to prove same-parity is transitive.
-- In reality it is, as if n and p share parity with m, and m's parity is unique.
-- Possible issues:
-- 1. I am missing a lemma which can generalize my cases and avoid impossible splits (i.e. (even m) and (odd m)).
-- 2. We have not learned enough about Agda to prove this yet (I think negations would simplify this greatly).
-- 3. One of my definitions is making the proof unncessarily hard (this is similar to how the right data structure simplifies an algorithm).
-- 4. Or of course, I'm just approaching the proof in the wrong way. :)
-- I will update this if I find a solution.
