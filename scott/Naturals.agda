module scott.Naturals where

-- A recursive definition for the natural numbers.
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- Allows Agda to optimize the internal representation of natural numbers.
-- suc (suc (suc (suc (... (suc zero))))) gives a unary representation of n, with size O(n).
-- BUILTIN NATURAL enables of binary representation of n, with space O(lg(n)).
{-# BUILTIN NATURAL ℕ #-}

-- Imports definitions for dealing with equality
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

-- Defines addition of natural numbers.
_+_ : ℕ → ℕ → ℕ
zero    + n = n
(suc n) + m = suc (n + m)

-- Explicit proof that 2 + 3 is equivalent to 5.
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

-- We can use refl to ask Agda to prove equivalence through term rewriting.
_ : 2 + 3 ≡ 5
_ = refl

-- (Practice) Explicit proof that 3 + 4 is equivalent to 7.
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    7
  ∎

-- We can extend addition to integer multiplication.
_*_ : ℕ → ℕ → ℕ
zero    * n = zero
(suc m) * n = n + (m * n)

-- An explicit proof that 2 * 3 is equivalent to 6.
_ : 2 * 3 ≡ 6
_ =
  begin
    2 * 3
  ≡⟨⟩
    3 + (1 * 3)
  ≡⟨⟩
    3 + (3 + (0 * 3))
  ≡⟨⟩
    3 + (3 + 0)
  ≡⟨⟩
    6
  ∎

-- (Practice) An explicit proof that 3 * 4 = 12.
_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    12
  ∎

-- (Exercise) We can also define exponetiation from multiplication.
_^_ : ℕ → ℕ → ℕ
n ^ zero    = (suc zero)
n ^ (suc m) = n * (n ^ m)

-- Sanity check that 4^3 is 64.
_ : 4 ^ 3 ≡ 64
_ =
  begin
    4 ^ 3
  ≡⟨⟩
    4 * (4 ^ 2)
  ≡⟨⟩
    4 * (4 * (4 ^ 1))
  ≡⟨⟩
    4 * (4 * (4 * (4 ^ 0)))
  ≡⟨⟩
    4 * (4 * (4 * 1))
  ≡⟨⟩
    64
  ∎

-- We now define monus: minus for natural numbers. There is a lower bound of zero.
-- This has recursion on the lhs and recursion on the rhs.
_∸_ : ℕ → ℕ → ℕ
m       ∸ zero    = m
zero    ∸ (suc n) = zero
(suc m) ∸ (suc n) = m ∸ n

-- Let's try substracting a larger number from a smaller number.
_ : 3 ∸ 5 ≡ 0
_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

-- Let's also try 5 ∸ 3.
_ : 5 ∸ 3 ≡ 2
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

-- We can simplify our proofs (programs) by giving precedence to operators.
infixl 6 _+_ _∸_
infixl 7 _*_

-- We can also give these operators efficient bitstring implementations.
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- Strech exercise: implement a base-two numeration system with basic operators.

-- The definition for a bitstring.
data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

-- Part 1: Define a suc operator for bitstrings.
inc : Bin → Bin
inc (rst O) = (rst I)
inc (res I) = ((inc res) O)
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

from_aux : Bin → ℕ → ℕ
from_aux (⟨⟩) (n)      = 0
from_aux ((rst I)) (n) = n + (from_aux (rst) (2 * n))
from_aux ((rst O)) (n) = from_aux (rst) (2 * n)

from : Bin → ℕ
from n = from_aux (n) (1)

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
