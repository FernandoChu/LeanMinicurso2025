import Mathlib
import Lean4MiniCurso.Sucesiones

/-!
# Continuidad y derivadas

En este archivo exploraremos los conceptos de estructuras y
clases en Lean, a través de ejemplos en álgebra abstracta.
-/


namespace Derivadas
noncomputable section

/-- El límite de una function f en un punto. -/
def IsLimitAt (f : ℝ → ℝ) (x₀ k : ℝ) : Prop :=
  ∀ ε, ∃ δ, ∀ x, |x₀ - x| < δ → |k - f x| < ε

notation3 "Lim" f "at" x₀ "⇝" k => IsLimitAt f x₀ k

lemma IsLimitAt.iff {f : ℝ → ℝ} {x₀ k : ℝ} :
    (Lim f at x₀ ⇝ k) ↔
      ∀ a : ℕ → ℝ, (Lim a ⇝ x₀) → (Lim (fun n ↦ f (a n)) ⇝ k) := by
  sorry

/--
Define what it means that `f` is continuous at `x` using the `ε`-`δ`-definition, i.e.
a function `f` is continuous at `x₀` if and only if
for every `ε > 0`, there exists a `δ > 0` such that for every `y : ℝ` with
`|x₀ - y| < δ`, it follows that `|f x₀ - f y| < ε`.
-/
def IsContinuousAt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  Lim f at x₀ ⇝ f x₀

def IsContinuous (f : ℝ → ℝ) : Prop :=
  ∀ x, IsContinuousAt f x

def IsDerivativeAt (f : ℝ → ℝ) (x k : ℝ) : Prop :=
  Lim (fun h ↦ (f (x + h) - f x)/h) at 0 ⇝ k

lemma IsDerivativeAt.sum (f g : ℝ → ℝ) (x₀ α β : ℝ)
    (hf : IsDerivativeAt f x₀ α) (hg : IsDerivativeAt f x₀ β) :
    IsDerivativeAt (f + g) x₀ (α + β) := by
  intro ε
  let c : ℝ := sorry
  use c
  intro h hc
  simp
  calc
    |α + β - (f (x₀ + h) + g (x₀ + h) - (f x₀ + g x₀)) / h|
        = |(α - (f (x₀ + h) - f x₀) / h) + (β - (g (x₀ + h) - g x₀) / h)| := by ring_nf
      _ ≤ |α - (f (x₀ + h) - f x₀) / h| + |β - (g (x₀ + h) - g x₀) / h| := by apply abs_add_le
      _ < ε := by sorry

lemma IsDerivativeAt.mul (f g : ℝ → ℝ) (x₀ α β : ℝ)
    (hf : IsDerivativeAt f x₀ α) (hg : IsDerivativeAt f x₀ β) :
    IsDerivativeAt (f * g) x₀ (α * g x₀ + f x₀ * β) := by
  rw [IsDerivativeAt]
  rw [IsLimitAt.iff]
  sorry

lemma IsDerivativeAt.continuousAt (f : ℝ → ℝ) (x y : ℝ) :
    IsDerivativeAt f x y → IsContinuousAt f x :=
  sorry

def IsDerivative (f f' : ℝ → ℝ) : Prop :=
  ∀ x, IsDerivativeAt f x (f' x)

structure 𝓒₁ : Type :=
  function : ℝ → ℝ
  deriv : ℝ → ℝ
  is_deriv : IsDerivative function deriv
  is_cont : IsContinuous deriv

instance : Coe 𝓒₁ (ℝ → ℝ) where
  coe f := f.function

def 𝓒₁.add (f g : 𝓒₁) : 𝓒₁ where
  function := f + g
  deriv := f.deriv + g.deriv
  is_deriv := sorry
  is_cont := sorry

/-!
## Ejercicios
Muestre que `𝓒₁` es un espacio vectorial sobre ℝ.
-/

/-
Lean se queja ante el siguiente código, que cree está pasando?
Enmiende el error. Sugerencia, cuál es la definición de `Module`?
-/
-- instance : Module 𝓒₁ ℝ := sorry
