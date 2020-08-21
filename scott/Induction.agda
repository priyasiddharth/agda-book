module scott.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

-- (Practice) Operators and rings.
-- 
-- LCM and * are two operators which are associative, commutative, and distribute.
-- Each of their identities is 1.
-- 
-- Function composition is associative ("(f of g) of h" is "f of (g of h)").
-- Function composition is not commutative (f(g(x)) is not g(f(x))).
-- Function composition has an identity (the identity function).

-- Let's test the associativity of _+_.
_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

-- There are infinitely many cases, so let's prove it inductively.
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

-- To prove commutivity we start with an identity lemma.
+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    (suc m) + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

-- Another lemma.
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
    (suc m) + (suc n)
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ∎

-- The proof of commutivity.
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + (suc n)
  ≡⟨ +-suc m n ⟩
    suc(m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc(n + m)
  ≡⟨⟩
    suc n + m
  ∎

-- Let's use commutivity to prove a novel rearrangement of parantheses.
+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩ -- applies associativity to terms n, n, (p + q)
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩ -- our proof for +-assoc is symmetric so we can prove the premise from the consequence
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    m + (n + p) + q
  ∎

-- (Strech) finite-+-assoc
finite-+-assoc-1 : ∀ (n p : ℕ) → 0 + (n + p) ≡ (0 + n) + p
finite-+-assoc-1 n p = refl
finite-+-assoc-2 : ∀ (n p : ℕ) → 1 + (n + p) ≡ (1 + n) + p
finite-+-assoc-2 n p = refl
finite-+-assoc-3 : ∀ (n p : ℕ) → 2 + (n + p) ≡ (2 + n) + p
finite-+-assoc-3 n p = refl
finite-+-assoc-4 : ∀ (n p : ℕ) → 3 + (n + p) ≡ (3 + n) + p
finite-+-assoc-4 n p = refl

-- We can also prove associativity using rewrite.
+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero    n p                        = refl -- this case is trivial and Agda can prove it automatically
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl -- if we simplify we get suc(X) = suc(P(X)), so we can rewrite using P

-- Let's prove commutivity the same way.
+-identity' : ∀ (n : ℕ) → n + zero ≡ n
+-identity' zero                          = refl
+-identity' (suc n) rewrite +-identity' n = refl

+-suc' : ∀ (m n : ℕ) → m + (suc n) ≡ suc (m + n)
+-suc' zero    n                    = refl
+-suc' (suc m) n rewrite +-suc' m n = refl

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero    rewrite +-identity' m            = refl
+-comm' m (suc n) rewrite +-suc' m n | +-comm' m n = refl -- we can chain together an arbitrary number of rewrites

-- (Exercise) m + (n + p) ≡ n + (m + p)
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ +-comm m (n + p) ⟩
    (n + p) + m
  ≡⟨ +-assoc n p m ⟩
    n + (p + m)
  ≡⟨ cong (n +_) (+-comm p m) ⟩
    n + (m + p)
  ∎

-- (Exercise) (m + n) * p ≡ m * p + n * p
-- TODO
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p =
  begin
    (zero + n) * p
  ≡⟨⟩
    n * p
  ≡⟨⟩
    zero + n * p
  ≡⟨⟩
    zero * p + n * p
  ∎
*-distrib-+ (suc m) n p =
  begin
    ((suc m) + n) * p
  ≡⟨⟩
    (suc (m + n)) * p
  ≡⟨⟩
    p + (m + n) * p
  ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + m * p) + n * p
  ≡⟨⟩
    (suc m) * p + n * p
  ∎

-- (Exercise) (m * n) * p ≡ m * (n * p)
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p =
  begin
    ((suc m) * n) * p
  ≡⟨⟩
    (n + m * n) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    n * p + (m * n) * p
  ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    n * p + m * (n * p)
  ≡⟨⟩
    (suc m) * (n * p)
  ∎

-- (Exercise) m * n ≡ n * m
*-identity : ∀ (m : ℕ) → m * zero ≡ zero * m
*-identity zero = refl
*-identity (suc m) =
  begin
    (suc m) * zero
  ≡⟨⟩
    zero + m * zero
  ≡⟨ cong (zero +_) (*-identity m) ⟩
    zero + zero * m
  ≡⟨⟩
    zero * (suc m)
  ∎

-- *-comm : ∀ (m n : ℕ) → m * n ≡ n * m
-- *-comm zero n rewrite *-identity n = refl

-- (Exercise) zero ∸ n ≡ zero
∸-lb : ∀ (n : ℕ) → zero ∸ n ≡ zero
∸-lb zero = refl
∸-lb (suc n) rewrite ∸-lb n = refl

-- (Exercise) n ∸ n ∸ p ≡ m ∸ (n + p)
-- TODO

-- (Exercise) Distributivity and associativity for ^ and +
-- TODO

-- (Exercise) Binary laws
-- TODO
