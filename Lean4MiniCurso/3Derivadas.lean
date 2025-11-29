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

lemma IsDerivativeAt.sum (f g : ℝ → ℝ) (x₀ d d' : ℝ)
    (hf : IsDerivativeAt f x₀ d) (hg : IsDerivativeAt f x₀ d') :
    IsDerivativeAt (f + g) x₀ (d + d') := by
  intro ε
  let c : ℝ := sorry
  use c
  intro h hc
  simp
  calc
    |d + d' - (f (x₀ + h) + g (x₀ + h) - (f x₀ + g x₀)) / h|
        = |(d - (f (x₀ + h) - f x₀) / h) + (d' - (g (x₀ + h) - g x₀) / h)| := by ring_nf
      _ ≤ |d - (f (x₀ + h) - f x₀) / h| + |d' - (g (x₀ + h) - g x₀) / h| := by apply abs_add_le
      _ < ε := by sorry

lemma IsDerivativeAt.mul (f g : ℝ → ℝ) (x₀ f'x g'x) :
    IsDerivativeAt (f * g) x₀ (f'x * g'x) := by
  rw [IsDerivativeAt]
  rw [IsLimitAt.iff]
  sorry

lemma IsDerivativeAt.continuousAt (f : ℝ → ℝ) (x y : ℝ) :
    IsDerivativeAt f x y → IsContinuousAt f x :=
  sorry

def IsDerivative (f f' : ℝ → ℝ) : Prop :=
  ∀ x, IsDerivativeAt f x (f' x)

def 𝓒₁ : Type := {f : ℝ → ℝ | ∃ f' : ℝ → ℝ, IsDerivative f f' ∧ IsContinuous f'}

def 𝓒₁.add (f g : 𝓒₁) : 𝓒₁ :=
  ⟨f.1 + g.1 , ⟨f.2 + g.2⟩⟩

lemma foooo (f g : D1) : HasDerivative (f.1 + g.1) := sorry

lemma foo' : IsDerivative (fun x ↦ x^2) (fun x ↦ 2 * x) :=
  sorry

/-!
## Ejercicios
Resuelva los siguientes ejercicios.
-/


def ContinuousAt' (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  sorry

lemma ContinuousAt_iff_ContinuousAt' (f : ℝ → ℝ) (x₀ : ℝ) :
    IsContinuousAt f x₀ ↔ ContinuousAt' f x₀ := by
  sorry
