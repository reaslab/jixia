/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
-/
open IO in
def hello : IO Unit :=
  println! "Hello, world!"

universe u
variable {α : Type u}

theorem eq_trans_sym {a b c : α} : a = b → b = c → c = a := by
  intro h₁ h₂
  rw [h₁, h₂]

theorem simp_test (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
    : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp
  assumption

theorem dsimp_test (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
    : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  dsimp
  simp
  assumption

/-- pow_succ x n = pow x n.succ -/
def pow_succ [Mul α] (x : α) : Nat → α
  | .zero => x
  | .succ n => pow_succ x n * x

structure FermatTriple (k : Nat) : Type where
  x : Nat
  y : Nat
  z : Nat
  eqn : x ^ k + y ^ k = z ^ k

example : FermatTriple 2 := ⟨ 3, 4, 5, rfl ⟩

namespace Option

inductive IsSome : Option α → Prop where
  | of_some : ∀ {a : α}, IsSome (some a)

inductive _root_.Sum.IsRight {β : Type _} : α ⊕ β → Prop where
  | of_right : ∀ {b : β}, IsRight (.inr b)

/-- A none is not a some -/
theorem neg_is_some_none : ¬IsSome (α := α) none := by sorry

instance : DecidablePred (IsSome (α := α)) := fun a =>
  match a with
  | some _ => .isTrue .of_some
  | none => .isFalse neg_is_some_none

end Option
