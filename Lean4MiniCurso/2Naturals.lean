import Mathlib

/-!
# Expresiones numéricas

En este archivo exploraremos los naturales, los enteros y los reales.
-/

/-!
## El tipo de los naturales ℕ

En Mathlib, tenemos el tipo de los naturales `ℕ : Type`.
Todas las operaciones y resultados básicos ya están en Mathlib, pero también podemos crear
nuestras propias definiciones o teoremas.

Tácticas generales:
- `rw [e]`, cuando `e : a = b`, cambia todas las ocurrencias de `a` por `b`.
- `rw [← e]`, cuando `e : a = b`, cambia todas las ocurrencias de `b` por `a`.
- `simp`, `ring` y `norm_num` prueban igualdades básicas.

Tácticas específicas para los naturales: Cuando `n : ℕ`
- `induction n with...` genera dos casos, el caso base y el caso sucesor.
-/

def add : ℕ → ℕ → ℕ :=
  fun n m ↦ match n with
  | 0 => m
  | .succ n => .succ (add n m)

#eval add 3 7
#eval add 3 0

/-- Igualdades que son por definición se prueban con `rfl` ("reflexividad"). -/
example : add 3 0 = 3 := by
  rfl

/-- Igualdades "abstractas" tienen que sor probadas por otros métodos, como inducción. -/
example (n : ℕ) : add n 0 = n := by
  induction n with
  | zero => rw [add]
  | succ n h =>
      rw [add]
      rw [h]

/-!
Por supuesto, no queremos reinventar la rueda. Tácticas como `simp` simplifican este tipo de
expresiones, si es que usamos la suma definida en la librería.
-/
example (n : ℕ) : n + 0 = n := by
  simp

/-!
## El tipo de los reales ℝ

También tenemos el tipo `ℝ` de los números reales en Lean. Notese que estos son los verdaderos
números reales, no una aproximación finita como la que se encuentra en otros lenguajes.

Estos son representados como sequencias de Cauchy.
-/

/- El número real `2` is representado por la secuencia Cauchy constante `2, 2, 2, ...`. -/
#eval (2 : ℝ)

/- Cuidado con las expresiones numericas, estas son por convención sobre los números naturales
salvo se especifique lo contrario. -/
example : 2 + 2 = 4 := by
  rfl

/- Para especificar que se requiere . -/
example : (2 : ℝ) + 2 = 4 := by
  norm_num

/- Identities with real variables can be proven using `rw` with lemmas from the library. -/
example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  rw [sq, sq, sq]
  rw [mul_add, add_mul, add_mul]
  rw [mul_comm y x, ← add_assoc, add_assoc (x * x)]
  rw [two_mul, add_mul]

/- La táctica `ring` prueba identidades básicas en semianillos. -/
example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

/- Mathlib también cuenta con otra funciones básicas, como el seno y coseno. -/
example (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
  rw [Real.sin_sq_add_cos_sq]


section Inequalities

/- The real numbers are ordered and we can use many lemmas from the library to close simple
goals. -/
example (x : ℝ) : x ≤ x := by
  apply le_refl

example {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply hxy
  · apply hyz

/-
We can find lemma names by using the library search tactic `exact?`.
-/
example (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  exact?

/- We can also use the trans tactic. -/
example {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  trans y
  · apply hxy
  · apply hyz

/- Or the calc tactic. -/
example {x y z : ℝ} (hxy : x ≤ y) (hyz : y = z) : x ≤ z := by
  calc
    x ≤ y := by apply hxy
    _ = z := by apply hyz

/- Or use `linarith` to close linear arithmetic goals. -/
example {x y z : ℝ} (hxy : x ≤ y) (hyz : y = z) : x ≤ z := by
  linarith

/- A slightly more complicated example. -/
example {a b : ℝ} : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
    calc
      a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
                              _ ≥ 0 := by positivity
  calc
    2 * a * b = 2 * a * b + 0 := by ring
            _ ≤ 2 * a * b + (a ^ 2 - 2 * a * b + b ^ 2) := by linarith
            _ = a ^ 2 + b ^ 2 := by ring

/- `gcongr` can be used to prove inequalities of expressions by showing
inequalities between subexpressions. -/
example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  gcongr

example {a b x c d : ℝ} (h1 : a + 1 ≤ b + 1) (h2 : c + 2 ≤ d + 2) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  gcongr x ^ 2 * ?_ + ?_
  · linarith
  · linarith

end Inequalities

section CaseSplitting

example (x y : ℝ) : x < |y| → x < y ∨ x < -y := by
  -- a new usage of the `obtain` tactic: We case split on an `or` statement.
  obtain (h|h) := le_or_gt 0 y
  -- step through this proof to observe.
  · rw [abs_of_nonneg h]
    intro h
    -- We want to show an `∨` statement, by showing the left case is true.
    left
    exact h
  · rw [abs_of_neg h]
    intro h
    -- We want to show an `∨` statement, by showing the right case is true.
    right
    exact h

end CaseSplitting

section Casting

/- Sometimes a Lean statement can fool the reader. Is the following true? -/
example (n : ℕ) : n - 1 + 1 = n := by
  sorry

/- It is false! This is because this uses subtraction in the natural numbers and there
`0 - 1 = 0`! -/
example : ∃ (n : ℕ), n - 1 + 1 ≠ n := by
  use 0
  simp

/- What we might mean instead is: -/
example (n : ℕ) : ((n : ℝ) - 1) + 1 = n := by
  simp

/-
What happens when we have `n : ℕ` and write `(n : ℝ)`?
Lean knows how to convert a natural number to a real number, this is called *casting*.
-/
example (n : ℕ) : ℝ := n

/- Casts can be very annoying to deal with! -/
example (n : ℕ) (hn : 1 ≤ n) :
    Real.sin (n.choose 2) = Real.sin (n * (n - 1) / 2) := by
  by_cases h : n = 0
  · subst h
    simp
  · congr
    rw [Nat.choose_two_right]
    rw [Nat.cast_div]
    · rw [Nat.cast_mul, Nat.cast_two]
      rw [Nat.cast_sub, Nat.cast_one]
      apply hn
    · rw [← even_iff_two_dvd]
      apply Nat.even_mul_pred_self n
    · simp

/-
Division by `0` is allowed in Lean. Why?

When we write `/`, we don't want to always pass a proof that the denominator is non-zero.
Instead, we allow division by zero and provide a "junk value". In this case,
we arbitrarily chose `1 / 0 = 0`.

Of course, division does not satisfy the property `x * 1 / x = 1` for every `x`, but only
for whenever `x ≠ 0`. Hence, many theorems will have non-zero assumptions, but this does not
stop us from having a definition of `1 / 0`.
-/
example : 1 / 0 = 0 := rfl

example : ∃ (x : ℝ), x * (1 / x) ≠ 1 := by
  use 0
  simp

example (x : ℝ) (hx : 0 ≠ x) : x * (1 / x) = 1 := by
  apply mul_one_div_cancel hx.symm

end Casting

section Sequences

/- A sequence of real numbers is a function `ℕ → ℝ`. -/
variable (a : ℕ → ℝ)

/- The `5`-th entry of the sequence `a` is simply `a 5`. -/
/--
info: a 5 : ℝ
-/
#guard_msgs in
#check a 5

/--
The sequence `a : ℕ → ℝ` converges to `x : ℝ` if for every `ε > 0`,
there exists `n₀ : ℕ` such that for all `n ≥ n₀`, `|x - a n| ≤ ε`.
-/
def ConvergesTo (a : ℕ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ (n₀ : ℕ), ∀ n ≥ n₀, |x - a n| ≤ ε

/- Use `rw [convergesTo_iff]` to unfold the definition of convergence. -/
lemma convergesTo_iff (a : ℕ → ℝ) (x : ℝ) :
    ConvergesTo a x ↔ ∀ ε > 0, ∃ (n₀ : ℕ), ∀ n ≥ n₀, |x - a n| ≤ ε := by
  rfl

/-- Any constant sequence converges to its value. -/
lemma ConvergesTo.const (a : ℝ) : ConvergesTo (fun _ ↦ a) a := by
  rw [convergesTo_iff]
  intro ε hε
  use 0
  simp only [ge_iff_le, zero_le, sub_self, abs_zero, forall_const]
  linarith

example : ConvergesTo (fun n ↦ 1 / n) 0 := by
  intro ε hε
  use ⌈1 / ε⌉₊
  intro n hn
  simp only [one_div, zero_sub, abs_neg]
  have : n ≥ ε⁻¹ := by
    rw [inv_eq_one_div]
    exact Nat.ceil_le.mp hn
  rw [abs_inv]
  simp only [Nat.abs_cast, ge_iff_le]
  exact inv_le_of_inv_le₀ hε this

/-- If `a` converges to `x` and `b` converges to `y`, then
`a + b` converges to `x + y`. -/
lemma ConvergesTo.add {a b : ℕ → ℝ} {x y : ℝ}
    (ha : ConvergesTo a x) (hb : ConvergesTo b y) :
    ConvergesTo (a + b) (x + y) := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := ha (ε / 2) (by linarith)
  obtain ⟨m₀, hm₀⟩ := hb (ε / 2) (by linarith)
  use n₀ + m₀
  intro n hn
  have h1 : |x - a n| ≤ ε / 2 := by
    apply hn₀
    linarith
  have h2 : |y - b n| ≤ ε / 2 := by
    apply hm₀
    linarith
  calc
    |x + y - (a + b) n| = |x + y - (a n + b n)| := by rfl
                      _ = |(x - a n) + (y - b n)| := by ring_nf
                      _ ≤ |x - a n| + |y - b n| := by exact abs_add_le _ _
                      _ ≤ ε / 2 + ε / 2 := by exact add_le_add h1 h2
                      _ = ε := by simp

/--
The sequence `a : ℕ → ℝ` is bounded if there exists a constant `M : ℝ` such that
`|a n| ≤ M` for all `M`.
-/
def Bounded (a : ℕ → ℝ) : Prop :=
  ∃ (M : ℝ), ∀ n, |a n| ≤ M

lemma bounded_iff (a : ℕ → ℝ) :
    Bounded a ↔ ∃ (M : ℝ), ∀ n, |a n| ≤ M := by
  rfl

/--
If `a : ℕ → ℝ` is bounded by `M` for almost all `n : ℕ`, it is bounded
everywhere.
-/
lemma Bounded.of_le {a : ℕ → ℝ} (M : ℝ) (n₀ : ℕ) (h : ∀ n ≥ n₀, |a n| ≤ M) :
    Bounded a := by
  rw [bounded_iff]
  let s : Finset ℕ := Finset.range (n₀ + 1)
  use M + s.sup' ⟨0, by simp [s]⟩ (fun k ↦ |a k|)
  intro m
  by_cases hm : n₀ ≤ m
  · trans
    · exact h m hm
    · simp only [le_add_iff_nonneg_right, Finset.le_sup'_iff]
      use 0
      simp [s]
  · have hmem : m ∈ s := by simp [s]; omega
    trans
    · exact Finset.le_sup' (fun k ↦ |a k|) hmem
    · have : 0 ≤ M := (abs_nonneg (a n₀)).trans (h n₀ (Nat.le_refl n₀))
      simpa

/-- Any convergent sequence is bounded. -/
lemma ConvergesTo.bounded {a : ℕ → ℝ} {x : ℝ} (h : ConvergesTo a x) :
    Bounded a := by
  obtain ⟨n₀, hn₀⟩ := h 1 (by linarith)
  apply Bounded.of_le (|x| + 1) n₀
  intro n hn
  specialize hn₀ n hn
  calc
    |a n| = |(a n - x) + x| := by ring_nf
        _ ≤ |a n - x| + |x| := by apply abs_add
        _ = |x - a n| + |x| := by rw [abs_sub_comm]
        _ ≤ 1 + |x| := by linarith
        _ = |x| + 1 := by ring

/-- If `a` converges to `x` and `b` converges to `y`, then `a * b` converges
to `x * y`. -/
lemma ConvergesTo.mul {a b : ℕ → ℝ} {x y : ℝ} (ha : ConvergesTo a x)
    (hb : ConvergesTo b y) :
    ConvergesTo (a * b) (x * y) := by
  intro ε hε
  obtain ⟨M, hM⟩ := ha.bounded
  let C : ℝ := |M| + |y| + 1
  have : 0 < C := by dsimp only [C]; positivity
  obtain ⟨n₀, hn₀⟩ := ha (ε / (2 * C)) (by positivity)
  obtain ⟨m₀, hm₀⟩ := hb (ε / (2 * C)) (by positivity)
  use max n₀ m₀
  intro n hn
  have : 0 ≤ |M| := by positivity
  have : 0 ≤ |y| := by positivity
  have : |y| ≤ C := by dsimp only [C]; linarith
  have : |a n| ≤ C := by
    trans |M|
    · trans M
      apply hM
      exact le_abs_self M
    · dsimp [C]
      linarith
  calc
    |x * y - (a * b) n| = |x * y - a n * b n| := by rfl
                      _ = |(x - a n) * y + a n * (y - b n)| := by ring_nf
                      _ ≤ |(x - a n) * y| + |a n * (y - b n)| := by apply abs_add
                      _ = |x - a n| * |y| + |a n| * |y - b n| := by rw [abs_mul, abs_mul]
                      _ ≤ ε / (2 * C) * C + C * (ε / (2 * C)) := ?_
                      _ = ε := by field_simp; ring
  gcongr ?_ * ?_ + ?_ * ?_
  · apply hn₀
    exact le_of_max_le_left hn
  · apply hm₀
    exact le_of_max_le_right hn
