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
def identity (A : Type) : A → A := fun x ↦ x

/- La aplicación de una función es entonces "aplicar la regla". -/
#eval identity ℕ 2


/-
## Tipos inductivos
Los tipos inductivos son tipos libremente generados por *constructores*.
El tipo inductivo más famoso es el tipo ℕ.
-/

namespace TiposInductivos

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

inductive Prod (A B : Type) where
  | pair (a : A) (b : B) : Prod A B

def flip : Prod ℕ ℕ → Prod ℕ ℕ :=


inductive Eq {α : Type} : α → α → Prop where
  | refl : (a : α) → Eq a a
