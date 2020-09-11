module scott.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)

-- A relation to order ℕ.
data _≤_ : ℕ → ℕ → Set where
  -- The proposition (0 ≤ n) always holds.
  z≤n : ∀ {n : ℕ} → (zero ≤ n)
  -- The proposition (m ≤ n) is proof that (suc m ≤ suc n)
  s≤s : ∀ {m n : ℕ} → (m ≤ n) → (suc m ≤ suc n)

-- An example proof using a relational data type.
-- The use of {n : ℕ} rather than (n : ℕ) allows for 2 to bind to z≤n implicitly.
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

-- An explicit form of the proof
_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

-- We can also give precedence to relational types.
-- The lower the level, the less tight the binding, so 1 + 2 ≤ 4 gives ((1 + 2) ≤ 4)
infix 4 _≤_

-- This definition is correct but impractical without some lemmas.
-- For instance, proving that (1000 ≤ 2000) requires 1000 applications of s≤s or z≤n.
-- Let's prove that (suc m ≤ suc n) entails (m ≤ n).
-- Note that m≤n is a variable name. It is the proposition used to prove (suc m ≤ suc n).
inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

-- We can invert any relation. Let's show that this is so with z≤n.
inv-z≤n : ∀ {m : ℕ} → m ≤ zero → m ≡ zero
inv-z≤n z≤n = refl

-- (Exercise) Let's think about different properties of relations.
--
-- 1. Construct a preorder which is not a partial order.
--
-- There are many orders we can place on strings. One such order is the length order. We
-- write u ≤ v if the length of u is less than or equal to the length of v.
-- * This is a preorder because (1) length(u) ≤ length(u), and (2) if length(u) ≤ length(v),
--   and length(v) is ≤ length(w), then length(u) ≤ length(w).
-- * This is not a partial order because u ≤ v ≤ u simply implies that length(u) ≤ length(v).
--   We cannot conclude u ≡ v.
--
-- 2. Construct a partial order which is not a total order.
--
-- Let's consider subset containment. This is a partial order which is not a total order.
-- * This is a partial order because (from set theory) (1) S ⊆ S, (2) S ⊆ T ⊆ U ⇒ S ⊆ U,
--   and (3) S ⊆ U ⊆ S ⇒ S ≡ S.
-- * Let's say S ≡ { 1 } and T ≡ { 2 }. Then neither S ⊆ T nore T ⊆ S hold. This is not a
--   total order.
--
-- Note: Proving these facts after this lession could make a nice exericse.

-- We know that ≤ is reflexive. That is to say, x ≤ x. Let's prove that.
≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl

-- It is also useful to have the transitivity of ≤ as a relation.
--
-- To understand this definition, remember that (m ≤ n) is a type. The definition says that
-- given a type (m ≤ n) and (n ≤ p), we can deduce the type (m ≤ p).
--
-- [A note on automated reasoning in Agda]
-- In this proof we have considered the cases where:
-- * argument 1 has type z≤n while argument 2 has any type.
-- * argument 1 has type s≤s while argument 2 has type s≤s.
-- That is to say, we ignore the case:
-- * argument 1 has type s≤s while argument 2 has type z≤n.
-- Note that in such a case we have s≤s derived from writing n as (suc n'). We also have
-- z≤n derived from writing n as zero. This implies that zero ≡ (suc n'), which contradicts
-- the structure of ℕ. Agda can detect such contradicts, and omit such cases.
≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

-- Let's rewrite this using explicit arguments.
≤-trans' : ∀ (m n p : ℕ) → m ≤ n → n ≤ p → m ≤ p
≤-trans' zero    _       _       z≤n       _         = z≤n
≤-trans' (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans' m n p m≤n n≤p)

-- Next we can show that ≤ is antisymmetric.
≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → n ≡ m
≤-antisym z≤n       z≤n       = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

-- (Exercise) Why can we omit (z≤n s≤s) and (s≤s z≤n). 
--
-- The reasoning for both cases is symmetric. Let's consider (z≤n s≤s). If we have that
-- z≤n we know that (m ≤ n) because (zero ≤ n). That is to say, m must be zero. However,
-- If we have s≤s to show that (n ≤ m). That is to say, there exists some m' such that
-- m ≡ (suc m'). As before, this contradicts the assumption that (m ≡ zero).

-- We now want to show that ≤ is a total order. That is m ≤ n or (inclusively) n ≤ n.
-- However, this is a structural property. We capture this structure using a new type.
data Total-LtEq (m n : ℕ) : Set where
  forward-lteq : m ≤ n → Total-LtEq m n -- Given the type m ≤ n, we can derive a type of (Total-LtEq m n).
  reverse-lteq : n ≤ n → Total-LtEq m n -- Given the type n ≤ m, we can derive a type of (Total-LtEq m n).

-- So what does it mean to show that ≤ is total? We need to show that (∀ m n : ℕ), either
-- m ≤ n or n ≤ m. By construction, we can deduce (Total-LtEq m n) only if m ≤ n or n ≤ m.
-- We can therefore state the totality of ≤ as a problem of type deduction.
≤-total : ∀ (m n : ℕ) → Total-LtEq m n
≤-total zero    n                          = forward-lteq z≤n
≤-total (suc m) zero                       = reverse-lteq z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                     | forward-lteq m≤n = forward-lteq (s≤s m≤n)
...                     | reverse-lteq n≤m = reverse-lteq (s≤s n≤m)

-- We can view the `with` statement as semantic sugar for one or more `where` definitions.
≤-total' : ∀ (m n : ℕ) → Total-LtEq m n
≤-total' zero n          = forward-lteq z≤n
≤-total' m zero          = reverse-lteq z≤n
≤-total' (suc m) (suc n) = helper (≤-total' m n)
  where
  -- This helper consumes a type from (Total m n) and uses it to deduce a type from (Total (suc m) (suc n)).
  -- Each case in this helper is a case in our `with` statement.
  helper : Total-LtEq m n → Total-LtEq (suc m) (suc n)
  helper (forward-lteq m≤n) = forward-lteq (s≤s m≤n)
  helper (reverse-lteq n≤m) = reverse-lteq (s≤s n≤m)

-- Now let's prove monotonicity wrt. + and ≤. We do this in several
-- parts.

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n
  -- 1. We can introduce the type of (p + m ≤ p + n) by invoking +-monoʳ-≤.
  -- 2. We can then obtain (m + p ≤ p + n) by the rewrite rule (+-comm m p).
  -- 3. We can then obtain (m + p ≤ n + p) by the rewrite rule (+-comm n p).

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)
  -- 1. We introduce the type of (m + p ≤ n + p) by (+-monoˡ-≤ m n p m≤n).
  -- 2. We introduce the type of (n + p ≤ n + q) by (+-monoʳ-≤ n p q p≤q).
  -- 3. By ≤-trans, (m + p ≤ n + p) and (n + p ≤ n + q) yields (m + p ≤ n + q).

-- (Strech) Prove *-mono-≤.

*-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ zero    p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)
  -- 1. We introduce the type of (n * q ≤ n * p) by inductive hypothesis.
  -- 2. We introduce the type of (q + n * q ≤ p + n * p) by +-mono-≤ with p≤q.
  -- 3. By definition (suc n) * q ≡ q + n * q and (suc n) * p ≡ p + n * p.

*-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

-- What about strict equality?

infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  -- The infimum of suc applied to ℕ is (suc zero), hence zero ≮ zero.
  z<s : ∀ {n : ℕ} → zero < (suc n)
  s<s : ∀ {m n : ℕ} → m < n → (suc m) < (suc n)

data Weak-Trichotomy-Lt (m n : ℕ) : Set where
  forward-lt  : m < n → Weak-Trichotomy-Lt m n
  reverse-lt  : n < m → Weak-Trichotomy-Lt m n
  identity-lt : m ≡ n → Weak-Trichotomy-Lt m n

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s       (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

<-weak-trichotomy : ∀ (m n : ℕ) → Weak-Trichotomy-Lt m n
<-weak-trichotomy zero    (suc n)                   = forward-lt  z<s
<-weak-trichotomy (suc m) zero                      = reverse-lt  z<s
<-weak-trichotomy zero    zero                      = identity-lt refl
<-weak-trichotomy (suc m) (suc n) with <-weak-trichotomy m n
...                               | forward-lt  m<n = forward-lt  (s<s m<n)
...                               | reverse-lt  n<m = reverse-lt  (s<s n<m)
...                               | identity-lt m≡n = identity-lt (cong suc m≡n)

+-monoʳ-< : ∀ (m p q : ℕ) → p < q → m + p < m + q
+-monoʳ-< zero    p q  p<q = p<q
+-monoʳ-< (suc m) p q p<q = s<s (+-monoʳ-< m p q p<q)

+-monoˡ-< : ∀ (m n q : ℕ) → m < n → m + q < n + q
+-monoˡ-< m n q m<n rewrite +-comm n q | +-comm m q = +-monoʳ-< q m n m<n

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = (<-trans (+-monoʳ-< m p q p<q) (+-monoˡ-< m n q m<n))

≤-if-< : ∀ {m n : ℕ} → m < n → (suc m) ≤ n
≤-if-< z<s       = (s≤s z≤n)
≤-if-< (s<s m<n) = s≤s (≤-if-< m<n)

<-if-≤ : ∀ {m n : ℕ} → (suc m) ≤ n → m < n
<-if-≤                 (s≤s z≤n) = z<s
<-if-≤ {suc m} {suc n} (s≤s m≤n) = s<s (<-if-≤ m≤n)

<-over-suc : ∀ {m n : ℕ} → (suc m) < n → m < n
<-over-suc (s<s z<s)       = z<s
<-over-suc (s<s (s<s m<n)) = s<s (<-over-suc (s<s m<n))

<-trans-revisited : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans-revisited m<n n<p = <-over-suc (<-if-≤ (≤-trans (s≤s (≤-if-< m<n)) (≤-if-< n<p)))

-- We now look at parity of numbers. This involves mutual recursivity.

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero : even zero
  suc  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc : ∀ {n : ℕ} → even n → odd (suc n)

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m  → even n → odd (m + n)

e+e≡e zero     en = en
e+e≡e (suc om) en = suc (o+e≡o om en)
o+e≡o (suc em) en = suc (e+e≡e em en)

o+o≡e : ∀ {m n : ℕ} → odd m  → odd n → even (m + n)
e+o≡o : ∀ {m n : ℕ} → even m → odd n → odd (m + n)

o+o≡e (suc em) on = suc (e+o≡o em on)
e+o≡o zero     on = on
e+o≡o (suc om) on = suc (o+o≡e om on)
