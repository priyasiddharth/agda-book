module scott.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import scott.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open scott.Isomorphism.≃-Reasoning

-- Here we define logic conjunction as a Cartesian product of propositions.
data _x_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A x B
infixr 2 _x_

proj₁ : ∀ {A B : Set} → A x B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} → A x B → B
proj₂ ⟨ x , y ⟩ = y

η-x : ∀ {A B : Set} (w : A x B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-x ⟨ x , y ⟩ = refl

-- While these propositions do not "obey" assoc/comm, they are equiasatisfiable.
-- This is equivalent to the notion of assoc/comm up to isomorphism.
x-comm : ∀ {A B : Set} → A x B ≃ B x A
x-comm =
  record
    { to      = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from    = λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to = λ{ ⟨ x , y ⟩ → refl }
    ; to∘from = λ{ ⟨ y , x ⟩ → refl }
    }

x-assoc : ∀ {A B C : Set} → (A x B) x C ≃ A x (B x C)
x-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

-- Exercise 1.
⇔≃x : ∀ {A B : Set} → (A ⇔ B) ≃ (A → B) x (B → A)
⇔≃x =
  record
    { to      = λ{ p → ⟨ _⇔_.to p , _⇔_.from p ⟩ }
    ; from    = λ{ ⟨ p , q ⟩ → record { to = p ; from = q } }
    ; from∘to = λ{ p → refl }
    ; to∘from = λ{ ⟨ p , q ⟩ → refl }
    }

-- Next we move onto truth as unitary structure.
data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
-- In this case, only one pattern can be matched, namely, tt.
-- Matching this pattern finishes the proof.
-- However, we cannot decide arbitrary problems over the space of patterns.
-- Therefore, we must introduce this pattern explicitly.
η-⊤ tt = refl

⊤-identityˡ : ∀ {A : Set} → ⊤ x A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

⊤-identityʳ : ∀ {A : Set} → A x ⊤ ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A x ⊤)
  ≃⟨ x-comm ⟩
    (⊤ x A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎
