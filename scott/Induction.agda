module scott.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import scott.Binary using (Bin; ⟨⟩; _I; _O; inc; to; from)

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
*-identity : ∀ (m : ℕ) → (suc zero) * m ≡ m
*-identity zero = refl
*-identity (suc m) =
  begin
    (suc zero) * (suc m)
  ≡⟨⟩
    (suc m) + zero * (suc m)
  ≡⟨⟩
    (suc m) + zero
  ≡⟨ +-comm (suc m) zero ⟩
    zero + (suc m)
  ≡⟨⟩
    (suc m)
  ∎

*-zero : ∀ (m : ℕ) → zero * m ≡ m * zero
*-zero zero = refl
*-zero (suc m) =
  begin
    zero * (suc m)
  ≡⟨⟩
    zero + zero * m
  ≡⟨ cong (zero +_) (*-zero m) ⟩
    zero + m * zero
  ∎

*-suc : ∀ (m n : ℕ) → m * (suc n) ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n =
  begin
    (suc m) * (suc n)
  ≡⟨⟩
    (suc n) + m * (suc n)
  ≡⟨ cong ((suc n) +_) (*-suc m n) ⟩
    (1 + n) + (m + m * n)
  ≡⟨ cong (_+ (m + m * n)) (+-comm 1 n) ⟩
    (n + 1) + (m + m * n)
  ≡⟨ +-assoc n 1 (m + m * n) ⟩
    n + ((suc m) + m * n)
  ≡⟨ sym (+-assoc n (suc m) (m * n)) ⟩
    (n + (suc m)) + m * n
  ≡⟨ cong (_+ (m * n)) (+-comm n (suc m)) ⟩
    ((suc m) + n) + m * n
  ≡⟨ +-assoc (suc m) n (m * n) ⟩
    (suc m) + (n + m * n)
  ∎

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n =
  begin
    zero * n
  ≡⟨ *-zero n ⟩
    n * zero
  ∎
*-comm (suc m) n =
  begin
    (suc m) * n
  ≡⟨⟩
    n + m * n
  ≡⟨ cong (n +_) (*-comm m n) ⟩
    n + n * m
  ≡⟨ sym (*-suc n m) ⟩
    n * (suc m)
  ∎

-- (Exercise) zero ∸ n ≡ zero
∸-lb : ∀ (n : ℕ) → zero ∸ n ≡ zero
∸-lb zero = refl
∸-lb (suc n) rewrite ∸-lb n = refl

-- (Exercise) m ∸ n ∸ p ≡ m ∸ (n + p)
∸-over-+ : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-over-+ m zero p = refl
∸-over-+ zero n p =
  begin
    (zero ∸ n) ∸ p
  ≡⟨ cong (_∸ p) (∸-lb n) ⟩
    zero ∸ p
  ≡⟨ ∸-lb p ⟩
    zero
  ≡⟨ sym (∸-lb (n + p)) ⟩
    zero ∸ (n + p)
  ∎
∸-over-+ (suc m) (suc n) p =
  begin
    (suc m) ∸ (suc n) ∸ p
  ≡⟨⟩
    m ∸ n ∸ p
  ≡⟨ ∸-over-+ m n p ⟩
    m ∸ (n + p)
  ∎

-- (Exercise) Distributivity and associativity for ^ and +
_^_ : ℕ → ℕ → ℕ
n ^ zero    = suc zero
n ^ (suc m) = n * (n ^ m)

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p =
  begin
    m ^ (zero + p)
  ≡⟨⟩
    m ^ p
  ≡⟨ sym (*-identity (m ^ p)) ⟩
    (suc zero) * (m ^ p)
  ∎
^-distribˡ-+-* m (suc n) p =
  begin
    m ^ ((suc n) + p)
  ≡⟨⟩
    m ^ (suc(n + p))
  ≡⟨⟩
    m * m ^ (n + p)
  ≡⟨ cong (m *_) (^-distribˡ-+-* m n p) ⟩
    m * (m ^ n * m ^ p)
  ≡⟨ sym (*-assoc m (m ^ n) (m ^ p)) ⟩
    (m * m ^ n) * m ^ p
  ≡⟨⟩
    (m ^ (suc n)) * (m ^ p)
  ∎

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) =
  begin
    (m * n) ^ (suc p)
  ≡⟨⟩
    (m * n) * ((m * n) ^ p)
  ≡⟨ cong ((m * n) *_) (^-distribʳ-* m n p) ⟩
    (m * n) * ((m ^ p) * (n ^ p))
  ≡⟨ cong ((m * n) *_) (*-comm (m ^ p) (n ^ p)) ⟩
    (m * n) * ((n ^ p) * (m ^ p))
  ≡⟨ *-assoc m n ((n ^ p) * (m ^ p)) ⟩
    m * (n * ((n ^ p) * (m ^ p)))
  ≡⟨ cong (m *_) (sym (*-assoc n (n ^ p) (m ^ p))) ⟩
    m * ((n * n ^ p) * m ^ p)
  ≡⟨⟩
    m * ((n ^ (suc p)) * (m ^ p))
  ≡⟨ cong (m *_) (*-comm (n ^ (suc p)) (m ^ p)) ⟩
    m * ((m ^ p) * (n ^ (suc p)))
  ≡⟨ sym (*-assoc m (m ^ p) (n ^ (suc p))) ⟩
    (m * (m ^ p)) * (n ^ (suc p))
  ≡⟨⟩
    (m ^ (suc p)) * (n ^ (suc p))
  ∎
