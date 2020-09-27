import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _≤_; _<_)
module bin where
data Bin : Set where
  <> : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc   : Bin → Bin
inc <> = <> I
inc (a O) = a I
inc (a I) = (inc (a)) O

to    : ℕ → Bin
to zero = <>
to (suc n) = inc (to n)

from  : Bin → ℕ
from <> = zero
from (a O) = 2 * from(a)
from (a I) = suc(2 * from(a))

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
incsuc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
incsuc <> = refl
incsuc (b O) = refl
incsuc (b I) rewrite incsuc b | +-suc (from b) ( from b + 0) = refl

fromto : ∀ (n : ℕ) → from (to n) ≡ n
fromto zero = refl
fromto (suc n) rewrite incsuc (to n) | fromto n = refl

data One : Bin → Set
data One where
       base : One (<> I)

       incone : ∀ {b : Bin}
             → One (b)
             ------------
             → One (inc b)

data Can : Bin → Set
data Can where
  zero :
          ---------
          Can (<>)



  one : ∀ {b : Bin}
          → One (b)
          ----------
          → Can (b)

inccan : ∀ {b : Bin}
   → Can b
   → Can (inc b)

inccan zero = one base
inccan (one oneb) = one (incone oneb)

toncan : ∀ (n : ℕ) → Can (to n)
toncan zero =  zero
toncan (suc n) = inccan (toncan n)

--- It was suggested in plfa to prove this theorem. However, I do not see the purpose
oneblt1 : ∀ (b : Bin) → (One b) → 1 ≤ (from b)
oneblt1 = {!!}
---- don't understand why termination check is failing.
---- In the input, I have (inc b) and x is a proof of One b. So why can't I say candin b one x ?
canidn : ∀ (b : Bin) → Can b → b ≡ to (from b)
canidn .<> zero = refl
canidn .(<> I) (one base) = refl
canidn .(inc b) (one (incone {b} x)) rewrite incsuc b | sym (canidn b (one x))  = refl

open import isomorphism using (≲)
-- isomorphism._≲_ (ℕ Bin)
ℕ≲Bin : isomorphism._≲_ ℕ Bin
ℕ≲Bin = record { to = to ; from = from ; from∘to = fromto }
