import Mathlib

def double (n : ℕ) : ℕ := n * 2

def factorial (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 5

def IsPrime (n : ℕ) : Prop :=
  n ≠ 1 ∧
  ∀ a b, (a * b = n) → (a = 1 ∨ b = 1)

example : ¬ (IsPrime 4) := by
  rw [IsPrime]
  simp
  use 2, 2
  trivial

theorem infinite_primes : ∀ n : ℕ, ∃ p ≥ n, IsPrime p := by
  intro n
  by_contra h
  simp at h
  apply h (factorial n + 1)
  · sorry
  · rw [IsPrime]
    constructor
    · sorry
    · intro a b eq
      by_cases ha : a ∣ factorial n
      · left
        apply Nat.eq_one_of_dvd_one
        rw [Nat.dvd_add_iff_right ha]
        use b
        rw [eq]
      · sorry
