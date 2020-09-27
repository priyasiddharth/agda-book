import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
module isomorphism where
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

≃-refl : ∀ {A : Set}
    -----
  → A ≃ A
≃-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    ; to∘from = λ{y → refl}
    }
≃-sym : ∀ {A B : Set}
  → A ≃ B
    -----
  → B ≃ A
to (≃-sym A≃B) = from A≃B
from (≃-sym A≃B) = to A≃B
from∘to (≃-sym A≃B) = to∘from A≃B
to∘from (≃-sym A≃B) = from∘to A≃B

≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
to (≃-trans A≃B B≃C) = (to B≃C) ∘ (to (A≃B))
from (≃-trans A≃B B≃C) = (from A≃B) ∘ (from B≃C)
from∘to (≃-trans A≃B B≃C) x  rewrite (from∘to B≃C (to A≃B x)) | from∘to A≃B x = refl
to∘from (≃-trans A≃B B≃C) x  rewrite (to∘from A≃B (from B≃C x)) | to∘from B≃C x = refl

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_
≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
    { to      = λ{x → to   B≲C (to   A≲B x)}
    ; from    = λ{y → from A≲B (from B≲C y)}
    ; from∘to = λ{x →
        begin
          from A≲B (from B≲C (to B≲C (to A≲B x)))
        ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
          from A≲B (to A≲B x)
        ≡⟨ from∘to A≲B x ⟩
          x
        ∎}
     }

≃-implies-≲ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≲ B
to (≃-implies-≲ A≃B) = to(A≃B)
from (≃-implies-≲ A≃B) = from(A≃B)
from∘to (≃-implies-≲ A≃B) = from∘to(A≃B)

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

⇔-refl : ∀ {A : Set} → A ⇔ A
_⇔_.to ⇔-refl = λ x → x
_⇔_.from ⇔-refl = λ x → x

⇔-sym : ∀ {A B : Set} →
    A ⇔ B
  -------
  → B ⇔ A
_⇔_.to (⇔-sym A⇔B) = _⇔_.from(A⇔B)
_⇔_.from (⇔-sym A⇔B) = _⇔_.to(A⇔B)

⇔-trans : ∀ {A B C : Set} →
    A ⇔ B
  → B ⇔ C
  → A ⇔ C
_⇔_.to (⇔-trans A⇔B B⇔C) = _⇔_.to(B⇔C) ∘ _⇔_.to A⇔B
_⇔_.from (⇔-trans A⇔B B⇔C) = (_⇔_.from A⇔B) ∘ (_⇔_.from B⇔C)
