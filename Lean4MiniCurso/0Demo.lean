import Mathlib

def double (n : ℕ) : ℕ := n * 2

def factorial (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 5

notation n "!" => factorial n

#eval 5 !

def IsPrime (n : ℕ) : Prop :=
  n ≠ 1 ∧
  ∀ a b, (a * b = n) → (a = 1 ∨ b = 1)

example : ¬ (IsPrime 4) := by
  rw [IsPrime]
  simp
  use 2, 2
  trivial

theorem factorial_pos : ∀ n, 0 < n ! := by
  intro n
  induction n with
  | zero => trivial
  | succ n ih =>
      rw [factorial]
      apply Nat.mul_pos
      · exact Nat.succ_pos _
      · apply ih

#check Nat.Prime
