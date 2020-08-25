module scott.Bool where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

-- This file exemplifies the differences between constructors and functions.
-- The or operation/constructor is excluded to simplify proofs.

-- Defining boolean types with boolean operators as functions.
data Bool : Set where
  true  : Bool
  false : Bool

and : Bool → Bool → Bool
and false x     = false
and x     false = false
and true  true  = true

not : Bool → Bool
not true  = false
not false = true

nand : Bool → Bool → Bool
nand x y = (not (and x y))

-- Proof 1.
-- A proof that (nand (nad x y) (nand x y)) ≡ (and x y) using boolean types.
-- Note that (and x y), (or x y), and (not x) are functions, not constructors.
-- Therefore, there are only 2 types to consider: true and false.
nands-to-ands : ∀ (x y : Bool) → (nand (nand x y) (nand x y)) ≡ (and x y)
nands-to-ands true  true  = refl -- (and true true) is a special case
nands-to-ands false x     = refl -- (and false x) is always false.
nands-to-ands true  false = refl -- this is the only remaining case.

-- Defining boolean expressions structurally.
data Expr : Set where
  elit : Bool -> Expr
  eand : Expr -> Expr -> Expr
  enot : Expr -> Expr

eval : Expr → Bool
eval (elit x)   = x
eval (eand x y) = and (eval x) (eval y)
eval (enot x)   = not (eval x)

enand : Expr → Expr → Expr
enand x y = (enot (eand x y))

lemma-1 : ∀ (x : Bool) → (and x false) ≡ false
lemma-1 false = refl
lemma-1 true  = refl

lemma-2 : ∀ (x : Expr) → (eval (eand x (elit false))) ≡ false
lemma-2 x =
  begin
    eval (eand x (elit false))
  ≡⟨⟩
    and (eval x) false
  ≡⟨ lemma-1 (eval x) ⟩
    false
  ∎

proj-1 : Expr → Bool → Bool
proj-1 x y = not (and (not y) (not (and (eval x) false)))

proj-2 : Bool → Bool
proj-2 x = not (and true (not x))

-- Proof 2.
-- A partial proof that (enand (enand x y) (enand x y)) evaluates to (and x y).
-- This proof was written with the same structure as proof 1, though it is no longer sufficient.
--
-- Unlike the previous proof, (enand x y), (eor x y), and (enot x) are types.
-- There is an countably infinite number of types not, resulting in more cases.
--
-- In addition, the case enands-to-eands x (elit false) is no longer trivial.
enands-to-eands : ∀ (x y : Expr) → (eval (enand (enand x y) (enand x y))) ≡ (eval (eand x y))
enands-to-eands (elit true) (elit true) = refl
enands-to-eands (elit false) y = refl
enands-to-eands x (elit false) =
  begin
    eval (enand (enand x (elit false)) (enand x (elit false)))
  ≡⟨⟩
    not (and (not (and (eval x) false)) (not (and (eval x) false)))
  ≡⟨ cong (proj-1 x) (lemma-1 (eval x)) ⟩
    not (and true (not (and (eval x) false)))
  ≡⟨ cong proj-2 (lemma-1 (eval x)) ⟩
    false
  ≡⟨ sym (lemma-2 x) ⟩
    eval (eand x (elit false))
  ∎
