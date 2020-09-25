module scott.Binary where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (+-suc)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total;
                                       +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)

-- Strech exercise: implement a base-two numeration system with basic operators.

-- The definition for a bitstring.
data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

-- Part 1: Define a suc operator for bitstrings.
inc : Bin → Bin
inc (rst O) = (rst I)
inc (rst I) = ((inc rst) O)
inc ⟨⟩      = ⟨⟩ I

_ : inc ⟨⟩ ≡ ⟨⟩ I
_ = refl
_ : inc (⟨⟩ O O O O O) ≡ ⟨⟩ O O O O I
_ = refl
_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ = refl
_ : inc (⟨⟩ I O) ≡ ⟨⟩ I I
_ = refl
_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ = refl
_ : inc (⟨⟩ I O O) ≡ ⟨⟩ I O I
_ = refl
_ : inc (⟨⟩ I O I) ≡ ⟨⟩ I I O
_ = refl

-- Part 2: Define a conversion between ℕ and Bin.
to : ℕ → Bin
to (zero)  = ⟨⟩ O
to (suc n) = inc (to n)

_ : to 0 ≡ ⟨⟩ O
_ = refl
_ : to 1 ≡ ⟨⟩ I
_ = refl
_ : to 2 ≡ ⟨⟩ I O
_ = refl
_ : to 3 ≡ ⟨⟩ I I
_ = refl
_ : to 4 ≡ ⟨⟩ I O O
_ = refl
_ : to 5 ≡ ⟨⟩ I O I
_ = refl
_ : to 6 ≡ ⟨⟩ I I O
_ = refl

from : Bin → ℕ
from ⟨⟩      = 0
from (rst I) = 1 + (from rst) + (from rst)
from (rst O) = (from rst) + (from rst)

_ : from ⟨⟩ ≡ 0
_ = refl
_ : from (⟨⟩ O) ≡ 0
_ = refl
_ : from (⟨⟩ I) ≡ 1
_ = refl
_ : from (⟨⟩ I O) ≡ 2
_ = refl
_ : from (⟨⟩ I I) ≡ 3
_ = refl
_ : from (⟨⟩ I O O) ≡ 4
_ = refl
_ : from (⟨⟩ I O I) ≡ 5
_ = refl
_ : from (⟨⟩ I I O) ≡ 6
_ = refl
_ : from (⟨⟩ O O I I O) ≡ 6
_ = refl

-- (Exercise) Laws of binary conversion.
from-inc-≡-suc-from : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from-inc-≡-suc-from ⟨⟩ = refl
from-inc-≡-suc-from (b O) = refl
from-inc-≡-suc-from (b I) =
  begin
    from (inc (b I))
  ≡⟨⟩
    from ((inc b) O)
  ≡⟨⟩
    (from (inc b)) + (from (inc b))
  ≡⟨ cong (_+ (from (inc b))) (from-inc-≡-suc-from b) ⟩
    (suc (from b)) + (from (inc b))
  ≡⟨ cong ((suc (from b)) +_) (from-inc-≡-suc-from b) ⟩
    (suc (from b)) + (suc (from b))
  ≡⟨⟩
    suc ((from b) + (suc (from b)))
  ≡⟨ cong suc (+-suc (from b) (from b)) ⟩
    suc (suc ((from b) + (from b)))
  ≡⟨⟩
    suc (suc (from (b O)))
  ≡⟨⟩
    suc (from (b I))
  ∎

_ : to (from (⟨⟩ O O)) ≡ (⟨⟩ O)
_ = refl

from-inverts-to : ∀ (n : ℕ) → from (to n) ≡ n
from-inverts-to zero = refl
from-inverts-to (suc n) =
  begin
    from (to (suc n))
  ≡⟨⟩
    from (inc (to n))
  ≡⟨ from-inc-≡-suc-from (to n) ⟩
    suc (from (to n))
  ≡⟨ cong suc (from-inverts-to n) ⟩
    suc n
  ∎

-- (Excercise) Binary canonical forms.

data One : Bin → Set where
  unit : One (⟨⟩ I)
  ext0 : ∀ {w : Bin} → One w → One (w O)
  ext1 : ∀ {w : Bin} → One w → One (w I)

data Can : Bin → Set where
  cnil : Can(⟨⟩ O)
  cone : ∀ {w : Bin} → One w → Can w

_ : Can (⟨⟩ I O I I O)
_ = cone (ext0 (ext1 (ext1 (ext0 unit))))

_ : Can(⟨⟩ O)
_ = cnil

inc-preserves-one : ∀ {w : Bin} → One w → One (inc w)
inc-preserves-one unit      = ext0 unit
inc-preserves-one (ext0 ow) = ext1 ow
inc-preserves-one (ext1 ow) = ext0 (inc-preserves-one ow)

inc-preserves-can : ∀ {w : Bin} → Can w → Can (inc w)
inc-preserves-can cnil      = cone unit
inc-preserves-can (cone ow) = cone (inc-preserves-one ow)

nonzero-to-is-in-can : ∀ (n : ℕ) → One (to (suc n))
nonzero-to-is-in-can zero    = unit
nonzero-to-is-in-can (suc n) = inc-preserves-one (nonzero-to-is-in-can n)

to-is-in-can : ∀ (n : ℕ) → Can (to n)
to-is-in-can zero    = cnil
to-is-in-can (suc n) = cone (nonzero-to-is-in-can n)

O-mono-≤ : ∀ (w : Bin) → from w ≤ from (w O)
O-mono-≤ ⟨⟩    = z≤n
O-mono-≤ (w O) = +-mono-≤ (O-mono-≤ w) (O-mono-≤ w)
-- Note: (+-mono-≤ (≤-refl {1}) (O-mono-≤ w)) has type, 1 + 2 * (from w) ≤ 1 + 4 * (from w)
-- Note: (+-mono-≤ (z≤n {1}) (O-mono-≤ w)) has type, 2 * (from w) ≤ 1 + 4 * (from w)
O-mono-≤ (w I) = +-mono-≤ (+-mono-≤ (≤-refl {1}) (O-mono-≤ w)) (+-mono-≤ (z≤n {1}) (O-mono-≤ w))

I-mono-≤ : ∀ (w : Bin) → from w ≤ from (w I)
I-mono-≤ w = +-mono-≤ (z≤n {1}) (O-mono-≤ w)

one→nonzero : ∀ {w : Bin} → One w → 1 ≤ from w
one→nonzero unit      = s≤s z≤n
one→nonzero {w O} (ext0 ow) = ≤-trans (one→nonzero ow) (O-mono-≤ w)
one→nonzero {w I} (ext1 ow) = ≤-trans (one→nonzero ow) (I-mono-≤ w)

--to-inverts-from-one : ∀ (w : Bin) → One w → to (from w) ≡ w
--to-inverts-from-one w     unit      = refl
--to-inverts-from-one (w I) (ext1 wo) =
--  begin
--    to (from (w I))
--  ≡⟨⟩
--    inc (to (from (w O)))
--  ≡⟨⟩
--    inc (to ((from w) + (from w)))
--  ∎

--to-inverts-from-can : ∀ (w : Bin) → Can w → to (from w) ≡ w
--to-inverts-from-can (⟨⟩ O) cnil      = refl
--to-inverts-from-can w      (cone ow) = to-inverts-from-one w ow

-- Proof of embedding from ℕ to Bin.

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    forward : A → B
    reverse : B → A
    inverse : ∀ (x : A) → reverse (forward x) ≡ x
open _≲_

ℕ-embeds-Bin : ℕ ≲ Bin
ℕ-embeds-Bin =
  record
    { forward = to
    ; reverse = from
    ; inverse = from-inverts-to
    }
