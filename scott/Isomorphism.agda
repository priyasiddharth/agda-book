module scott.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- Let's start with some auxilliary knowledge. First, we have lambda exprs.
-- Lambdas allow us to define one-off functions where they are needed.d
-- Obviously, in principle, named functions are just bound lambdas.

lambda : ℕ → ℕ
lambda = λ { zero → zero; y → suc y }

_ : lambda zero ≡ zero
_ = refl

_ : lambda 1 ≡ 2
_ = refl

_ : lambda 2 ≡ 3
_ = refl

-- We also need function composition. For now, we can define that.

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) = λ x → g (f x)

-- Extensionality asserts that two functions are equal if you cannot applications.
-- We can ask Agda to assume the axiom of extensionality.
-- A meta-proof exists to show extensionality is consistent with typed lambda calculus.
-- This means that we can prove things which were untrue before.
-- However, we cannot derive a contradiction.

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x) → f ≡ g

-- An example of using extensionality...
-- Assume we have an operator _⊕_ which is a right-recursive version of _+_.
-- We can prove that: ∀ (m n : ℕ) → m ⊕ n ≡ m + n
-- Using extensionality, we can derive: _⊕_ ≡ _+_

_⊕_ : ℕ → ℕ → ℕ
m ⊕ zero    = m
m ⊕ (suc n) = suc (m ⊕ n)

same-plus : ∀ (m n : ℕ) → m ⊕ n ≡ m + n
same-plus m n rewrite +-comm m n = helper m n
  where
    helper : ∀ (m n : ℕ) → m ⊕ n ≡ n + m
    helper m zero    = refl
    helper m (suc n) = cong suc (helper m n)

≡-plus : _⊕_ ≡ _+_
≡-plus = extensionality (λ m → extensionality (λ n → same-plus m n))

-- We can also give a more generalized definition for dependant functions.
postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x) → f ≡ g

-- We now introduce the notion of isomorphisms.
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

≃-refl : ∀ {A : Set} → A ≃ A
≃-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{x → x}
    ; from∘to = λ{x → refl}
    ; to∘from = λ{x → refl}
    }

≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B =
  record
    { to      = from A≃B
    ; from    = to A≃B
    ; from∘to = to∘from A≃B
    ; to∘from = from∘to A≃B
    }

≃-trans : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C =
  record
    { to      = (to B≃C) ∘ (to A≃B)
    ; from    = (from A≃B) ∘ (from B≃C)
    ; from∘to = λ{x →
        begin
          (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
        ≡⟨⟩
          from A≃B (from B≃C (to B≃C (to A≃B x)))
        ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
          from A≃B (to A≃B x)
        ≡⟨ from∘to A≃B x ⟩
          x
        ∎}
    ; to∘from = λ{x →
        begin
          (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) x)
        ≡⟨⟩
          to B≃C (to A≃B (from A≃B (from B≃C x)))
        ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C x)) ⟩
          to B≃C (from B≃C x)
        ≡⟨ to∘from B≃C x ⟩
          x
        ∎}
    }

-- Let's set up equational reasoning for ≃.
module ≃-Reasoning where
  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set} → A ≃ B → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≃ B → B ≃ C → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set) → A ≃ A
  A ≃-∎ = ≃-refl
open ≃-Reasoning

-- We can also weaken isomorphisms to embeddings.
infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{x → x}
    ; from∘to = λ{x → refl}
    }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
    { to      = (_≲_.to B≲C) ∘ (_≲_.to A≲B)
    ; from    = (_≲_.from A≲B) ∘ (_≲_.from B≲C)
    ; from∘to = λ{x →
        begin
          (_≲_.from A≲B ∘ _≲_.from B≲C) ((_≲_.to B≲C ∘ _≲_.to A≲B) x)
        ≡⟨⟩
          _≲_.from A≲B (_≲_.from B≲C (_≲_.to B≲C (_≲_.to A≲B x)))
        ≡⟨ cong (_≲_.from A≲B) (_≲_.from∘to B≲C (_≲_.to A≲B x)) ⟩
          _≲_.from A≲B (_≲_.to A≲B x)
        ≡⟨ _≲_.from∘to A≲B x ⟩
          x
        ∎}
    }

≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B) → (B≲A : B ≲ A)
  → (_≲_.to A≲B ≡ _≲_.from B≲A) → (_≲_.from A≲B ≡ _≲_.to B≲A)
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to =
  record
    { to      = _≲_.to A≲B
    ; from    = _≲_.from A≲B
    ; from∘to = _≲_.from∘to A≲B
    ; to∘from = λ{ x →
        begin
          _≲_.to A≲B (_≲_.from A≲B x)
        ≡⟨ cong (_≲_.to A≲B) (cong-app from≡to x) ⟩
          _≲_.to A≲B (_≲_.to B≲A x)
        ≡⟨ cong-app to≡from (_≲_.to B≲A x) ⟩
          _≲_.from B≲A (_≲_.to B≲A x)
        ≡⟨ _≲_.from∘to B≲A x ⟩
          x
        ∎}
    }

-- Exercises.

≃-implies-≲ : ∀ {A B : Set} → A ≃ B → A ≲ B
≃-implies-≲ A≃B =
  record
    { to      = to A≃B
    ; from    = from A≃B
    ; from∘to = from∘to A≃B
    }

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

⇔-refl : ∀ {A : Set} → A ⇔ A
⇔-refl =
  record
    { to   = λ{x → x}
    ; from = λ{x → x}
    }

⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym A⇔B =
  record
    { to   = _⇔_.from A⇔B
    ; from = _⇔_.to A⇔B
    }

⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans A⇔B B⇔C =
  record
    { to   = (_⇔_.to B⇔C) ∘ (_⇔_.to A⇔B)
    ; from = (_⇔_.from A⇔B) ∘ (_⇔_.from B⇔C)
    }
