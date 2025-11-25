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

example : IsPrime 5 := by
  rw [IsPrime]
  simp
  aesop

theorem factorial_pos : ∀ n, 0 < n ! := by
  intro n
  induction n with
  | zero => trivial
  | succ n ih =>
      rw [factorial]
      apply Nat.mul_pos
      · exact Nat.succ_pos _
      · apply ih

theorem fac_big (n : ℕ) : n ≤ n ! + 1 := by
  induction n with
  | zero => trivial
  | succ n ih =>
      rw [factorial]
      simp
      cases n with
      | zero => trivial
      | succ n =>
        have ineq : (n + 1)! + 1 ≤ (n + 1 + 1) * (n + 1)! := by
          sorry
        omega

theorem exists_infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ IsPrime p :=
  let p := Nat.minFac (n ! + 1)
  have f1 : n ! + 1 ≠ 1 := by
    apply ne_of_gt
    apply Nat.succ_lt_succ
    apply factorial_pos _
  have pp : IsPrime p := Nat.minFac_prime f1
  have np : n ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ n ! := dvd_factorial (minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (Nat.minFac_dvd _)
      pp.not_dvd_one h₂
  ⟨p, np, pp⟩

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

#check Nat.Prime
