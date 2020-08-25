module scott.Symmetry where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)

-- The goal of this test was to determine if Agda allows for inconsistent inductive variables.
-- As suspected, it does not. Despite what our intuition might be, the proofs are not symmetric.
-- In this case, we have defined (suc x) + y to be suc (x + y). The operator is not symmetric by
-- definition. Instead, we rely on the lemma +-suc. This example also shows that such asymmetries
-- can yield different proofs simply by changing the inductive variable.
--
-- It's unclear whether or not Agda would support this if the function definition was structurally
-- symmetric. I can't think of any interesting examples with structurally symmetric operations.

+-assoc-alt-1 : ∀ (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
+-assoc-alt-1 zero y z = refl
+-assoc-alt-1 x (suc y) z =
  begin
    (x + (suc y)) + z
  ≡⟨ cong (_+ z) (+-suc x y) ⟩
    suc ((x + y) + z)
  ≡⟨ cong suc (+-assoc-alt-1 x y z) ⟩
    suc (x + (y + z))
  ≡⟨ sym (+-suc x (y + z)) ⟩
    x + ((suc y) + z)
  ∎

-- Note specifically that, +-assoc-alt 2 x zero z = refl, is no longer a valid proof.
+-assoc-alt-2 : ∀ (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
+-assoc-alt-2 x zero z =
  begin
    (x + zero) + z
  ≡⟨ cong (_+ z) (+-identityʳ x) ⟩
    x + (zero + z)
  ∎
+-assoc-alt-2 (suc x) y z =
  begin
    suc ((x + y) + z)
  ≡⟨ cong suc (+-assoc-alt-2 x y z) ⟩
    (suc x) + (y + z)
  ∎
