module scott.Groups where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)

-- Simple definition for an additive group on ℤ₃.

data ℤ₃ : Set where
  zero : ℤ₃
  one  : ℤ₃
  two  : ℤ₃

_+_ : ℤ₃ → ℤ₃ → ℤ₃
zero + zero = zero
zero + one  = one
zero + two  = two
one  + zero = one
one  + one  = two
one  + two  = zero
two  + zero = two
two  + one  = zero
two  + two  = one

invr : ℤ₃ → ℤ₃
invr zero = zero
invr one  = two
invr two  = one

+-has-left-invr : ∀ (a : ℤ₃) → (invr a) + a ≡ zero
+-has-left-invr zero = refl
+-has-left-invr one  = refl
+-has-left-invr two  = refl

+-has-right-invr : ∀ (a : ℤ₃) → a + (invr a) ≡ zero
+-has-right-invr zero = refl
+-has-right-invr one  = refl
+-has-right-invr two  = refl

+-has-left-identity : ∀ (a : ℤ₃) → zero + a ≡ a
+-has-left-identity zero = refl
+-has-left-identity one  = refl
+-has-left-identity two  = refl

+-has-right-identity : ∀ (a : ℤ₃) → a + zero ≡ a
+-has-right-identity zero = refl
+-has-right-identity one  = refl
+-has-right-identity two  = refl

+-assoc : ∀ (a b c : ℤ₃) → (a + b) + c ≡ a + (b + c)
+-assoc zero zero zero = refl
+-assoc zero zero one  = refl
+-assoc zero zero two  = refl
+-assoc zero one  zero = refl
+-assoc zero one  one  = refl
+-assoc zero one  two  = refl
+-assoc zero two  zero = refl
+-assoc zero two  one  = refl
+-assoc zero two  two  = refl
+-assoc one  zero zero = refl
+-assoc one  zero one  = refl
+-assoc one  zero two  = refl
+-assoc one  one  zero = refl
+-assoc one  one  one  = refl
+-assoc one  one  two  = refl
+-assoc one  two  zero = refl
+-assoc one  two  one  = refl
+-assoc one  two  two  = refl
+-assoc two  zero zero = refl
+-assoc two  zero one  = refl
+-assoc two  zero two  = refl
+-assoc two  one  zero = refl
+-assoc two  one  one  = refl
+-assoc two  one  two  = refl
+-assoc two  two  zero = refl
+-assoc two  two  one  = refl
+-assoc two  two  two  = refl

-- Basic definition of a group.

record Group (A : Set) : Set where
  field
    -- Note: the type of op ensures the closure of op.
    id    : A
    bop   : A → A → A
    neg   : A → A
    assoc : ∀ (a b c : A) → bop (bop a b) c ≡ bop a (bop b c)
    lid   : ∀ (a : A) → bop id a ≡ a
    rid   : ∀ (a : A) → bop a id ≡ a
    linvr : ∀ (a : A) → bop (neg a) a ≡ id
    rinvr : ∀ (a : A) → bop a (neg a) ≡ id

-- Proof that ℤ₃ is a group.

ℤ₃-is-a-group : Group ℤ₃
ℤ₃-is-a-group =
  record
    { id    = zero
    ; bop   = _+_
    ; neg   = invr
    ; assoc = +-assoc
    ; lid   = +-has-left-identity
    ; rid   = +-has-right-identity
    ; linvr = +-has-left-invr
    ; rinvr = +-has-right-invr
    }
