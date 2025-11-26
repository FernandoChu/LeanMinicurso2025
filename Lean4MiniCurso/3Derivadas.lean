import Mathlib
import Lean4MiniCurso.Sucesiones

namespace Derivadas
noncomputable section

def IsLimitAt (f : ℝ → ℝ) (x₀ k : ℝ) : Prop :=
  ∀ a : ℕ → ℝ,
    (ConvergesTo a x₀) → ConvergesTo (fun n ↦ f (a n)) k

notation3 "Lim" f "at" x₀ "⇝" k => IsLimitAt f x₀ k

/--
Define what it means that `f` is continuous at `x` using the `ε`-`δ`-definition, i.e.
a function `f` is continuous at `x₀` if and only if
for every `ε > 0`, there exists a `δ > 0` such that for every `y : ℝ` with
`|x₀ - y| < δ`, it follows that `|f x₀ - f y| < ε`.
-/
def ContinuousAt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  Lim f at x₀ ⇝ f x₀

/-- If `f` is continuous at `x₀` and `a` is a sequence converging to `x₀`, then
`n ↦ f (a n)` converges to `f x₀`. -/
lemma ContinuousAt.convergesTo {f : ℝ → ℝ} {x₀ : ℝ} (hf : ContinuousAt f x₀)
    {a : ℕ → ℝ} (ha : ConvergesTo a x₀) :
    ConvergesTo (fun n ↦ f (a n)) (f x₀) := by
  apply hf
  apply ha

/-- If for every sequence `a` converging to `x₀`, `n ↦ f (a n)` converges to `f x₀`, then
`f` is continuous at `x₀`. -/
lemma ContinuousAt.of_forall_convergesTo {f : ℝ → ℝ} {x₀ : ℝ}
    (H : ∀ {a : ℕ → ℝ} (ha : ConvergesTo a x₀), ConvergesTo (fun n ↦ f (a n)) (f x₀)) :
    ContinuousAt f x₀ :=
  sorry

/-- `f` is continuous at `x₀` if and only if when ever `a` converges to `x₀`,
the sequence `n ↦ f (a n)` converges to `f x₀`. -/
theorem ContinuousAt.iff_forall_convergesTo {f : ℝ → ℝ} {x₀ : ℝ} :
    ContinuousAt f x₀ ↔
      (∀ {a : ℕ → ℝ} (ha : ConvergesTo a x₀), ConvergesTo (fun n ↦ f (a n)) (f x₀)) :=
  sorry

def IsDerivativeAt (f : ℝ → ℝ) (x f'x : ℝ) : Prop :=
  Lim (fun h ↦ (f (x + h) - f x)/h) at 0 ⇝ f'x

lemma IsDerivativeAt.sum (f g : ℝ → ℝ) (x f'x g'x) :
    IsDerivativeAt (f + g) x (f'x + g'x) :=
  sorry

lemma IsDerivativeAt.prod (f g : ℝ → ℝ) (x f'x g'x) :
    IsDerivativeAt (f * g) x (f'x * g'x) :=
  sorry

lemma foo (f : ℝ → ℝ) (x y : ℝ) :
  IsDerivativeAt f x y → ContinuousAt f x := sorry

def IsDerivative (f f' : ℝ → ℝ) : Prop :=
  ∀ x, IsDerivativeAt f x (f' x)

def HasDerivative (f : ℝ → ℝ) : Prop :=
  ∃ f', IsDerivative f f'

def D1 : Type := {f : ℝ → ℝ | HasDerivative f}

def deriv : D1 → (ℝ → ℝ) :=
  fun ⟨f, h⟩ ↦ h.choose

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
    ContinuousAt f x₀ ↔ ContinuousAt' f x₀ := by
  sorry
