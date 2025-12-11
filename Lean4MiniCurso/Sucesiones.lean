import Mathlib

noncomputable section

/-!
# Sucesiones en los reales

En este archivo exploraremos conceptos básicos de sucesiones en los reales.
-/

/-!
## El tipo de los naturales ℕ

En Mathlib, tenemos el tipo de los naturales `ℕ : Type`.
Todas las operaciones y resultados básicos ya están en Mathlib, pero también podemos crear
nuestras propias definiciones o teoremas.

Tácticas generales:
- `rw [e]`, cuando `e : a = b`, cambia todas las ocurrencias de `a` por `b`.
  Cuando `e` es una definición, simplemente la expande.
- `rw [← e]`, cuando `e : a = b`, cambia todas las ocurrencias de `b` por `a`.
- `simp` simplifica expresiones.
- `ring` prueba igualdades básicas en (semi)anillos.

Tácticas específicas para los naturales: Cuando `n : ℕ`
- `induction n with...` genera dos casos, el caso base y el caso sucesor.
-/

def add : ℕ → ℕ → ℕ :=
  fun n m ↦ match n with
  | 0 => m
  | .succ n => .succ (add n m)

#eval add 3 7
#eval add 3 0

/- Igualdades que son por definición se prueban con `rfl` ("reflexividad"). -/
example : add 3 0 = 3 := by
  rfl

/- Igualdades "abstractas" tienen que sor probadas por otros métodos, como inducción. -/
example (n : ℕ) : add n 0 = n := by
  induction n with
  | zero => rw [add]
  | succ n h =>
      rw [add]
      rw [h]

/-!
La táctica `simp` simplifica expresiones, pero solo aplica con funciones de Mathlib.
-/
example (n : ℕ) : n + 0 = n := by
  simp

/- Identidades obvias son probadas por `ring`. -/
example (a b : ℕ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by
  ring



/-!
## El tipo de los reales ℝ

En Lean tenemos el tipo `ℝ` de los números reales en Lean. Nótese que estos son los verdaderos
números reales, no una aproximación finita como la que se encuentra en otros lenguajes.

Estos son representados como sucesiones de Cauchy.
-/

/- El número real `2` es representado por la sucesión Cauchy constante `2, 2, 2, ...`. -/
#eval (2 : ℝ)

#eval (Real.pi : ℝ)

/-
Mathlib también cuenta con las funciones básicas que uno esperaría, como el seno y coseno.
-/
example : ℝ → ℝ :=
  fun x ↦ Real.sin x


/-!
## Cómo encontrar nombres de definiciones y resultados?
Muchas definiciones tienen un nombre esperado, como `ℕ`, `+`, `ℝ`, etc. Pero otras no: `Real.sin`.
Podemos encontrar nombres de definiciones y lemas ("API") de varias maneras.
-/

/-
### Manera 1: loogle
En la página web https://loogle.lean-lang.org/ se pueden buscar definiciones y lemmas.
También se pueden realizar búsquedas con el siguiente comando:
-/
-- #loogle Real.sin

/-
### Manera 2: `exact?` y `apply?`
Si estas en medio de una prueba, `exact?` buscará un lemma que corresponda exactamente
al objetivo. `apply?` buscará un lemma que se pueda aplicar.
-/
example (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
  exact?

example (x : ℝ) : 2 * Real.sin x ^ 2 + 2 * Real.cos x ^ 2 = 2 := by
  apply?

/-
### Manera 3: `rw??`
Si estas en medio de una prueba, `rw??` te permite seleccionar la sub-expresión específica que
quieres modificar, y te brindará sugerencias.
Esta es una de las mejores formas.
-/
example (x : ℝ) : 2 * Real.sin x ^ 2 + 2 * Real.cos x ^ 2 = 2 := by
  rw??
  sorry


/-
## Sucesiones y convergencia
A modo de ejercicio, definiremos la noción de convergencia y probaremos algunos resultados básicos.

Tácticas generales:
- `have h : p := _`, creará como objetivo intermedio demostrar `p`, y le pondrá de nombre `h` a esta
  nueva prueba.
- `ring_nf`, pondrá expresiones de (semi)anillos en una forma normal.
- `linarith` prueba desigualdades de aritmética linear
- `calc?` permite crear (des)igualdades incrementalmente
-/

/- Una sucesión de números reales es una función `ℕ → ℝ`. -/
example : ℕ → ℝ :=
  fun n ↦ n^2

/--
Una sucesión `a : ℕ → ℝ` converge a `x : ℝ` si para todo `ε > 0`,
existe un `n₀ : ℕ` tal que para todo `n ≥ n₀`, `|x - a n| ≤ ε`.
-/
def ConvergesTo (a : ℕ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ (n₀ : ℕ), ∀ n ≥ n₀, |x - a n| ≤ ε

notation3 "Lim " a " ⇝ " x => ConvergesTo a x

/-- Una sucesión constante converge a su valor constante. -/
lemma ConvergesTo.const (c : ℝ) : Lim (fun _ ↦ c) ⇝ c := by
  rw [ConvergesTo]
  intro ε hε
  use 0
  simp
  linarith

/--
Si `a` converge a `x` y `b` converge a `y` entonces
`a + b` converge a `x + y`.
-/
lemma ConvergesTo.add {a b : ℕ → ℝ} {x y : ℝ}
    (ha : Lim a ⇝ x) (hb : Lim b ⇝ y) :
    Lim (a + b) ⇝ (x + y) := by
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
                      _ ≤ |x - a n| + |y - b n| := by apply abs_add_le
                      _ ≤ ε / 2 + ε / 2 := by exact add_le_add h1 h2
                      _ = ε := by simp

/-- La función 1/n converge hacia 0. -/
example : Lim (fun n ↦ 1 / n) ⇝ 0 := by
  intro ε hε
  use ⌈ε⁻¹⌉₊
  intro n hn
  simp
  have : n ≥ ε⁻¹ := by
    calc
      (n : ℝ) ≥ ⌈ε⁻¹⌉₊ := by exact Nat.cast_le.mpr hn
            _ ≥ ε⁻¹ := by exact Nat.le_ceil ε⁻¹
  exact inv_le_of_inv_le₀ hε this


/-!
## Ejercicios
Pruebe los siguientes resultados.
-/

/--
Una sucesión `a : ℕ → ℝ` es acotada si existe una constante `M : ℝ`
tal que `|a n| ≤ M` para todo `n`.
-/
def Bounded (a : ℕ → ℝ) : Prop :=
  ∃ (M : ℝ), ∀ n, |a n| ≤ M

/--
Si `a : ℕ → ℝ` está acotada por `M` para todo `n ≥ n₀`, entonces la sucesión entera está acotada.
-/
lemma Bounded.of_le {a : ℕ → ℝ} (M : ℝ) (n₀ : ℕ) (h : ∀ n ≥ n₀, |a n| ≤ M) :
    Bounded a := by
  rw [Bounded]
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

/-- Toda sequencia convergente está acotada. -/
-- Sugerencia: use el resultado previo.
lemma ConvergesTo.bounded {a : ℕ → ℝ} {x : ℝ} (h : Lim a ⇝ x) :
    Bounded a := by
  obtain ⟨n₀, hn₀⟩ := h 1 (by linarith)
  apply Bounded.of_le (|x| + 1) n₀
  intro n hn
  specialize hn₀ n hn
  calc
    |a n| = |(a n - x) + x| := by ring_nf
        _ ≤ |a n - x| + |x| := by apply abs_add_le
        _ = |x - a n| + |x| := by rw [abs_sub_comm]
        _ ≤ 1 + |x| := by linarith
        _ = |x| + 1 := by ring

/-- Si `a` converge a `x` y `b` converge a `y`, entonces `a * b` converge a `x * y`. -/
-- Sugerencia: use el resultado previo.
lemma ConvergesTo.mul {a b : ℕ → ℝ} {x y : ℝ} (ha : Lim a ⇝ x) (hb : Lim b ⇝ y) :
    Lim (a * b) ⇝ (x * y) := by
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
                      _ ≤ |(x - a n) * y| + |a n * (y - b n)| := by apply abs_add_le
                      _ = |x - a n| * |y| + |a n| * |y - b n| := by rw [abs_mul, abs_mul]
                      _ ≤ ε / (2 * C) * C + C * (ε / (2 * C)) := ?_
                      _ = ε := by field
  gcongr ?_ * ?_ + ?_ * ?_
  · apply hn₀
    exact le_of_max_le_left hn
  · apply hm₀
    exact le_of_max_le_right hn

/-- Toda sucesión constante está acotada. -/
lemma Bounded.const (x : ℝ) : Bounded (fun _ ↦ x) := by
  sorry

/-- Una sucesión `a` está acotada sí y solo sí la sucesión `|a i|` está acotada. -/
lemma Bounded.iff_bounded_abs {a : ℕ → ℝ} :
    Bounded a ↔ Bounded (fun n ↦ |a n|) :=
  sorry

/-- Si `a` converge a `x`, entonces `- (a i)` converge a `-x`. -/
lemma ConvergesTo.neg {a : ℕ → ℝ} {x : ℝ} (ha : Lim a ⇝ x) :
    ConvergesTo (-a) (-x) :=
  sorry

/-- Una sucesión `a` converge a cero si y solo si `|a i|` converge a cero. -/
lemma ConvergesTo.zero_iff_convergesTo_abs_zero (a : ℕ → ℝ) :
    (Lim a ⇝ 0) ↔ (Lim (fun n ↦ |a n|) ⇝ 0) := by
  sorry

/-- Una sucesión `a` converge a `x` si y solo si `i ↦ x - a i` converge a `0`. -/
lemma ConvergesTo.iff_convergesTo_sub_zero (a : ℕ → ℝ) (x : ℝ) :
    (Lim a ⇝ x) ↔ (Lim (fun n ↦ x - a n) ⇝ 0) := by
  sorry

/--
Sean `a`, `b` y `c` sucesiones con `a n ≤ b n ≤ c n`. Si `a` y `c` convergen a `x`,
entonces `b` también converge a `x`. -/
lemma ConvergesTo.sandwich (a b c : ℕ → ℝ) {x : ℝ}
    (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n)
    (ha : Lim a ⇝ x) (hc : Lim c ⇝ x) :
    Lim b ⇝ x := by
  sorry
