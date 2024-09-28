
inductive Nat6 where
  | zero : Nat6
  | succ : Nat6 -> Nat6

open Nat6 (zero succ)

namespace Nat6

def ofNat : (a : Nat) -> Nat6
  | Nat.zero => zero
  | Nat.succ x => succ (ofNat x)

instance (n : Nat) : OfNat Nat6 n where
  ofNat := ofNat n

def add : (a b : Nat6) -> Nat6
  | a, zero => a
  | a, succ b => succ (add a b)

instance : Add Nat6 where
  add := add

def mul : (a b : Nat6) -> Nat6
  | _, zero => zero
  | a, succ b => (mul a b) + a

instance : Mul Nat6 where
  mul := mul

def pred : (a : Nat6) -> Nat6
  | zero => zero
  | succ a => a

variable (a b c : Nat6)

theorem add_zero : a + zero = a := rfl
theorem add_succ : a + (succ b) = succ (a + b) := rfl

theorem zero_add : zero + a = a := by
  induction a with
  | zero => rfl
  | succ a h => rw [add_succ, h]

theorem succ_add : (succ a) + b = succ (a + b) := by
  induction b with
  | zero => rfl
  | succ b h => rw [add_succ, add_succ, h]

theorem one_eq_succ_zero : 1 = succ zero := by rfl

theorem one_add : 1 + a = a.succ := by
  rw [one_eq_succ_zero]
  rw [succ_add, zero_add]

theorem add_comm : a + b = b + a := by
  induction a with
  | zero => rw [add_zero, zero_add]
  | succ a h =>
    rw [succ_add, add_succ, h]

theorem add_assoc : a + (b + c) = (a + b) + c := by
  induction c with
  | zero => repeat rw [add_zero]
  | succ c h =>
    repeat rw [add_succ]
    rw [h]

theorem add_comm_left : a + (b + c) = b + (a + c) := by
  rw [add_assoc, add_assoc, add_comm b a]

theorem add_comm_right : c + a + b = c + b + a := by
  rw [<- add_assoc, <- add_assoc, add_comm b a]

theorem mul_zero : a * zero = zero := rfl
theorem mul_succ : a * b.succ = a * b + a := rfl

theorem zero_mul : zero * a = zero := by
  induction a with
  | zero => rfl
  | succ a h => rw [mul_succ, h]; rfl

theorem succ_mul : a.succ * b = a * b + b := by
  induction b with
  | zero => repeat rw [mul_zero]; rfl
  | succ b h =>
    repeat rw [mul_succ]
    rw [h, add_succ, add_succ, add_comm_right]

theorem mul_comm : a * b = b * a := by
  induction a with
  | zero => rw [zero_mul, mul_zero]
  | succ a h => rw [succ_mul, mul_succ, h]

theorem mul_add : a * (b + c) = a * b + a * c := by
  induction a with
  | zero => (repeat rw [zero_mul]); rfl
  | succ a h =>
    repeat rw [succ_mul]
    rw [h]
    repeat rw [add_assoc]
    rw [add_comm_right (a * c) b]

theorem add_mul : (b + c) * a = b * a + c * a := by
  rw [mul_comm, mul_add, mul_comm a b, mul_comm a c]

theorem mul_assoc : a * (b * c) = (a * b) * c := by
  induction c with
  | zero => repeat rw [mul_zero]
  | succ c h =>
    repeat rw [mul_succ]
    rw [mul_add, h]

theorem pred_zero : pred 0 = 0 := rfl
theorem pred_succ : pred (succ a) = a := rfl

theorem succ_eq_succ : a.succ = b.succ -> a = b := by
  intro h
  exact Nat6.noConfusion h id

theorem add_cancel_left : (a + b = a + c) <-> b = c := by
  constructor
  . intro h
    induction a with
    | zero =>
      repeat rw [zero_add] at h
      exact h
    | succ a i =>
      apply i
      repeat rw [succ_add] at h
      apply succ_eq_succ
      exact h
  . intro h; rw [h]

theorem add_cancel_right : (b + a = c + a) <-> b = c := by
  rw [add_comm b a, add_comm c a]
  apply add_cancel_left

end Nat6
