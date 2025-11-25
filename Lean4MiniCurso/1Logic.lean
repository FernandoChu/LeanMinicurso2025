import Mathlib

/-!
# Lógica en Lean

En este archivo exploraremos como escribir y probar proposiciones lógicas.
-/

/-!
## El tipo `Prop`

Lean está basado en teoría de tipos. En esta teoría, hay dos nociones claves:
- La noción de ser un tipo, entiéndase como ser un conjunto.
- La noción de pertenecer a un tipo `a : A`, entiéndase como `a ∈ A`.

En teoría tipos, todo objecto matemático tiene un único tipo. Las proposiciones no son la excepción.
Es decir, tenemos el tipo de proposiciones `Prop`.

Veamos unos ejemplos.
-/

/- La proposicion verdadera. -/
example : Prop := True

/- La proposicion falsa. -/
example : Prop := False

/- Podemos *definir* proposiciones falsas, pero no las podremos probar. -/
example : Prop := ∀ n : ℕ, n < 5

/- No podemos definir proposiciones sin sentido. -/
-- example : Prop := 3 + ∀ = 4

/- Dada una proposición `p`, podemos definir nueva proposición "p implica p". -/
example (p : Prop) : Prop := p → p

/-
Las proposiciones también son tipos. Por lo tanto, también tienen elementos: sus pruebas.
-/

example : Prop := 1 + 1 = 2

example : 1 + 1 = 2 := by
  trivial

/-!
## Conectores lógicos
En esta sección introduciremos los conectores lógicos básicos: `→`, `∀`, `∃`, `¬`, `∨`, `∧`.
-/

/-!
### Implicación
Tácticas generales:
- `exact h`, cuando `h` es una prueba del objetivo
- `·`, cuando hay multiples objetivos.
- `sorry`, cuando no quieres terminar una prueba

Tácticas específicas: Cuando tienes `p → q` en
- Las hipótesis: `apply h` aplicará la hipótesis `h` en el objetivo
- El objetivo: `intro a1 a2 ...` introducirá nuevas variables `a1`, `a2`, ...
-/

example (p : Prop) : p → p := by
  intro hp
  exact hp

example (p q : Prop) : p → (q → p) := by
  intro hp hq
  exact hp

/-
Nota: por convención, `→` asocia hacia la derecha.
-/
example (p q r : Prop) : (p → q) → (p → q → r) → (p → r) := by
  intro pq pqr hp
  apply pqr
  · exact hp
  · apply pq
    exact hp

/-
Observación: una prueba de `p → q` es una *función*!
Esta función mapea una prueba de `p` a una prueba de `q`!
-/
example (p : Prop) : p → p :=
  fun hp ↦ hp

example (p q : Prop) : p → (q → p) :=
  fun hp ↦ fun hq ↦ hp



/-!
### Quantificacion universal
Tenemos tambien el tipo de todos los tipos `Type`. Entiendase entonces `X : Type` como
"Sea X un conjunto".
Un predicado `P` sobre `X` es entonces una functión de `X` al tipo de proposiciones: `P : X → Prop`.
-/
example (X : Type) (p q : X → Prop) (h : ∀ x : X, p x → q x) :
    (∀ x : X, p x) → ∀ y : X, q y := by
  intro hp y
  apply h
  apply hp

/-
Observación: una prueba de `∀ x : X, P x` también es una *función*!
Esta función mapea cada elemento `x` de `X` a una prueba de `P x`!
-/
example : ∀ n : ℕ, 0 ≤ n :=
  fun n ↦ zero_le n



/-!
### Existenciales
Tácticas específicas: Cuando tienes `∃ x : X, P x` en
- Las hipótesis: `obtain ⟨c, pc⟩ := hp` obtendrá un `c : X` tal que `pc : P c`.
- El objetivo: `use c` para usará `c` para reducir el objetivo a `P c`.
-/

example : ∃ n : ℕ, n < 1 := by
  use 0
  trivial

example (X : Type) (P Q : X → Prop) (hpq : ∀ x : X, P x → Q x) (hp : ∃ x : X, P x) : ∃ x, Q x := by
  obtain ⟨x, px⟩ := hp
  use x
  apply hpq
  exact px

/-
Observación: una prueba de `∃ x : X, P x` es un *par*!
Este par consiste de un `x : X` y de una prueba `h : P x`.
-/
example : ∃ n : ℕ, n < 1 := ⟨0, zero_lt_one⟩



/-!
### Conjunciones
Tácticas específicas: Cuando tienes `p ∧ q` en
- Las hipótesis: `obtain ⟨hp, hq⟩ := hpq` obtendrá `hp : p` y `hq : q`.
- El objetivo: `constructor` construirá dos nuevos objetivos, `p` y `q`.
-/

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro pq
  obtain ⟨hp, hq⟩ := pq
  constructor
  · exact hq
  · exact hp

/-
Observación: una prueba de `p ∧ q` también es un *par*!
Este par consiste de una prueba `hp : p` y de una prueba `hq : q`.
-/
example (p q : Prop) : p ∧ q → q ∧ p := fun hpq ↦ ⟨hpq.right, hpq.left⟩


/-!
### Disyunciones
Tácticas específicas: Cuando tienes `p ∨ q` en
- Las hipótesis: `obtain hp | hq := hpq` generará dos casos, uno donde `hp : p` y otro donde `hq : q`.
- El objetivo: `left` para probar `p`, o `right` para probar `q`.
-/
example (p q : Prop) : p → p ∨ q := by
  intro hp
  left
  exact hp

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro pq
  obtain hp | hq := pq
  · right
    assumption
  · left
    assumption

/-
Observación: una prueba de `p ∨ q` es una prueba de `p` o una prueba de `q`.
Es decir, la disyunción es la unión de proposiciones!
-/
example (p q : Prop) : p → p ∨ q := fun hp ↦ .inl hp



/-!
### Bicondicionales
Tácticas específicas: Cuando tienes `p ↔ q` en
- Las hipótesis: `rw [hp]` remplazará `p` por `q` en el objetivo.
- El objetivo: `constructor` construirá dos nuevos objetivos, `p → q` y `q → p`.
-/

example (p q : Prop) : (p ↔ q) ↔ (p → q) ∧ (q → p) := by
  constructor
  · intro pq
    rw [pq]
    constructor
    · intro hq
      exact hq
    · intro hq
      exact hq
  · intro h
    constructor
    · exact h.left
    · exact h.right


/-! ### Negación
Dada una proposicion `p : Prop`, su negación `¬ p` está definida en Lean como `¬ p := p → False`.
-/
example (p q : Prop) (h : p → q) : ¬ q → ¬ p := by
  intro nq hp
  apply nq
  apply h
  exact hp

/-
Dada una contradicción, usando `exfalso`, podemos derivar cualquier cosa.
-/
example (p q : Prop) (hp : p) (np : ¬ p) : q := by
  exfalso
  apply np
  exact hp

/-
Nota: las tácticas `contrapose` y `push_neg` tabién son útiles.
-/
example (p q : Prop) (h : ¬ p → ¬ q) : q → p := by
  contrapose
  exact h

example (p : Prop) (hp : ¬ ¬ p) : p := by
  push_neg at hp
  exact hp



/-!
## Ejercicios
Trate de resolver los siguientes ejercicios usando tácticas o definiciones explícitas.
-/

example (p q r : Prop) : (p → q) → (p → r) → p → q := sorry


example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := sorry


example (p q r s : Prop) : (p → (q → r)) → (p → (r → s)) → (p → (q → s)) := sorry


example (p q : Prop) : (p → q) → (p → ¬ q) → ¬ p := sorry


example (α β : Type) (p : α → β → Prop) : (∀ x y, p x y) → ∀ y x, p x y := sorry


example (α : Type) (p q : α → Prop) :
    (∀ x, p x) → (∀ x, p x → q x) → ∀ x, q x := sorry


example (α β : Type) (p : α → β → Prop) (h : ∃ x, ∀ y, p x y) : ∀ y, ∃ x, p x y := sorry


example (α : Type) (p : α → Prop) (h : ∀ x, ¬ p x) : ¬ ∃ x, p x := sorry


example (α : Type) (p : α → Prop) (h : ∃ x, ¬ p x) : ¬ ∀ x, p x := sorry


example (α : Type) (p : α → Prop) (h : ¬ ∀ x, p x) : ∃ x, ¬ p x := sorry


example (α : Type) (p : α → Prop) (h : ¬ ∃ x, p x) : ∀ x, ¬ p x := sorry


example (p q q' : Prop) (h : p ∧ q) (hq : q → q') : p ∧ q' := sorry


example (p : Prop) (h : p ∨ p) : p := sorry


example (α : Type) (p : α → Prop) (q : Prop) (h : ∃ x, p x ∨ q) : (∃ x, p x) ∨ q := sorry


example (p q r : Prop) (hpq : p ↔ q) (hqr : q ↔ r) : p ↔ r := sorry
