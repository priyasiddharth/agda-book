module scott.Binary where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

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
