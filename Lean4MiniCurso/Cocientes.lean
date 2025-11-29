import Mathlib

noncomputable section
namespace Estructuras

/-!
# Álgebra abstracta, estructuras y clases

En este archivo exploraremos los conceptos de estructuras y
clases en Lean, a través de ejemplos en álgebra abstracta.
-/


namespace Quotients

/-
Besides the `structure` command, there is a different way to construct new types:
By taking quotients by equivalence relations.
-/

/-- A relation on integers: Two integers are equivalent if and only if their difference is
divisible by `n`. -/
def Rel (n : ℤ) (x y : ℤ) : Prop := n ∣ x - y

/-- `Rel` is an equivalence relation. -/
lemma Rel.equivalence (n : ℤ) : Equivalence (Rel n) where
  refl x := by simp [Rel]
  symm {x y} hxy := by
    dsimp [Rel] at *
    rw [dvd_sub_comm]
    exact hxy
  trans {x y z} hxy hyz := by
    dsimp [Rel] at *
    obtain ⟨k, hk⟩ := hxy
    obtain ⟨m, hm⟩ := hyz
    use k + m
    linarith

/-- An equivalence relation on `ℤ`. -/
def modSetoid (n : ℤ) : Setoid ℤ where
  r := Rel n
  iseqv := Rel.equivalence n

/-- The type of integers modulo `n`: The quotient of `ℤ` by the relation `Rel`. -/
abbrev Mod (n : ℤ) : Type :=
  Quotient (modSetoid n)

/-- An addition on the integers modulo `n`. -/
instance (n : ℤ) : Add (Mod n) where
  add := by
    /- We use the universal property of the quotient: To define a function out of `Mod n`, it suffices
    to define a function out of `ℤ` that is constant on equivalence classes.
    `⟦x⟧` (type with `\[[` and `\]]`) is notation for the image of `x` in the quotient `Mod n`.
    -/
    apply Quotient.lift₂ (fun x y ↦ ⟦x + y⟧)
    intro x y z w hxz hyw
    obtain ⟨k, hk⟩ := hxz
    obtain ⟨m, hm⟩ := hyw
    /- To show two representatives are equal in the quotient, it suffices to show they are related. -/
    apply Quotient.sound
    use k + m
    linarith

end Quotients
