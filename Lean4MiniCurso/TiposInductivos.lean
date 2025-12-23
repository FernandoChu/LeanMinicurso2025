import Mathlib

/-!
# Cómo funciona Lean?

Como ya mencionamos, Lean está basado en teoría de tipos. Lastimosamente
no alcanza tiempo para estudiar a detalle esta teoría, pero deberían tener
ya una idea intuitiva de esta.

Parecería ser una teoría complicada: tenemos funciones, productos,
naturales, estructuras, etc.

En realidad, solo se necesitan tres componentes: Universos, funciones y
tipos inductivos.
-/


/-
## La jerarquia de universos
Intuitivamente, `Prop` es el universo de proposiciones. `Type n` es un
universo de conjuntos de una cardinalidad menor al n-ésimo cardinal inaccesible.
-/

#check Prop
#check Type
#check Type 1

#check ℕ → Type


/-
## Funciones
A diferencia de las funciones que uno ve en teoría de conjuntos, usalmente
definidas como relaciones, las funciones en teoría de tipos son un concepto
base, es decir no están definidas en términos de otros conceptos.

Su uso es más cercano a la intuición matemática: una función es una "regla".
-/
def identity (A : Type) : A → A :=
  fun x ↦ x

/- La aplicación de una función es entonces "aplicar la regla". -/
#eval identity ℕ 2


/-
## Tipos inductivos
Los tipos inductivos son tipos libremente generados por *constructores*.
Esto es análogo al grupo libre generado por ciertos elementos.
-/

namespace TiposInductivos

/-
### El tipo de los naturales
-/
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

def plus : Nat → Nat → Nat :=
  fun n m ↦ match n with
  | .zero => m
  | .succ n => .succ (plus n m)

def ind (P : Nat → Prop) (h0 : P .zero) (hd : ∀ n : Nat, P n → P (.succ n)) :
  ∀ n, P n :=
  fun n ↦ match n with
  | .zero => h0
  | .succ n => hd n (ind P h0 hd n)

#eval plus (.succ .zero) .zero

example (n : Nat) :
    plus n .zero = n := by
  induction n with
  | zero => rw [plus]
  | succ n h =>
      rw [plus]
      rw [h]

/-
### Productos
-/
inductive Prod (A B : Type) where
  | pair (a : A) (b : B) : Prod A B

def flip : Prod ℕ ℕ → Prod ℕ ℕ :=
  fun p ↦ match p with
  | .pair a b => .pair b a

/- Debería ser claro que todas las estructuras siguen este patrón. -/


/-
### El tipo de igualdades
-/
inductive Eq {α : Type} : α → α → Prop where
  | refl : (a : α) → Eq a a

/-
Esta definición no debería ser sorpresa: esta definiendo la relación de
igualdad como la "mínima relación reflexiva"!
-/

/- Substituir propiedades es dado por recursión! -/
def subst (a b : ℕ) (h : Eq a b) (P : ℕ → Prop) (ha : P a) : P b :=
  match h with
  | .refl _ => ha

/- La táctica `rw` solo está aplicando esta función subst. -/
example (a b c : ℕ) (h1 : Eq a b) (h2 : Eq a c) : Eq b c :=
  subst a b h1 (fun x ↦ Eq x c) h2

/-!
## Ejercicios
Defina otros tipos inductivos que conoce (primero tiene que *re*conocerlos!),
y pruebe resultados básicos de estos.
Algunas ideas:
- El tipo de listas de elementos de un tipo `X`
- El tipo de árboles binarios de un tipo `X`
- La desigualdad de los naturales.
- Curioso: Fijemos `n : ℕ`. El tipo de números naturales multiplos de `n`
  se puede definir también como un tipo inductivo.
- Curioso: Los enteros también pueden definirse como un tipo inductivo.
  Solución: Revise la definición de Mathlib `#check ℤ`.
-/
