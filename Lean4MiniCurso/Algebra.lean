import Mathlib

noncomputable section
namespace Estructuras

/-!
# Álgebra abstracta, estructuras y clases

En este archivo exploraremos los conceptos de estructuras y
clases en Lean, a través de ejemplos en álgebra abstracta.
-/

/-
## Estructuras

A modo de ejemplo, consideremos el círculo de radio 1 en ℝ.
El tipo que consiste de estos puntos podría definirse así:
-/
def MyCircle : Type :=
  {⟨a,b⟩ : ℝ × ℝ | a^2 + b^2 = 1}

/-
Nótese que un elemento de este tipo es una *tupla* `(z,h)`.
En particular, obtener la coordenada `x`, tendríamos que escribir:
-/
def xCoordinate (p : MyCircle) : ℝ := p.1.1

/- Para crear un punto en `MyCircle` tendriamos que escribir: -/
def northPole : MyCircle := ⟨⟨0, 1⟩, by simp⟩

/-
En vez de realizar estas operaciones, podemos usar *estructuras*
-/
structure Circle where
  x : ℝ
  y : ℝ
  h : x ^ 2 + y ^ 2 = 1 := by simp

example (p : Circle) : ℝ := p.x

example : Circle := {
  x := 0
  y := 1
}

example : Circle := ⟨0, 1, by simp⟩

/-
De hecho, el producto cartesiano está definido como una estructura!
Ejercicio: cuál estructura?
-/

#check Prod

/-
## Namespaces
Poder escribir `p.x` se debe a un patrón más general:
- Dado un tipo `X`
- Dada una definición llamada `X.algo`
- Dado un elemento `x : X`
Entonces podemos usar *dot notation* ("notación de punto") y escribir
`x.algo` en vez de `X.algo x`.
-/

#check Circle.x

def Circle.angle (p : Circle) : ℝ := Real.arctan (p.y / p.x)

example (p : Circle) : ℝ := p.angle

/-
## Álgebra abstracta
Con las estructuras en mano, podemos definir por ejemplo el tipo de monoides.
-/

structure Monoide where
  carrier : Type
  op : carrier → carrier → carrier
  unit : carrier
  op_assoc (a b c : carrier) : op (op a b) c = op a (op b c)
  op_unit (a : carrier) : op a unit = a
  unit_op (a : carrier) : op unit a = a

#check Monoide.op

notation3 x " ⋄ " y => Monoide.op _ x y

lemma unit_unit (M : Monoide) : (M.unit ⋄ M.unit) = M.unit := by
  rw [M.op_unit]

/- Podemos definir el monoide de los naturales -/
def NatMonoide : Monoide := {
  carrier := ℕ
  op a b := a + b
  unit := 0
  op_assoc a b c := by ring
  op_unit a := by ring
  unit_op a := by ring
}

/- Y usar resultados abstractos en circunstancias específicas. -/
example : (NatMonoide.unit ⋄ NatMonoide.unit) = NatMonoide.unit := by
  rw [unit_unit]

/- Note que no podemos escribir lo siguiente: -/
-- example : (0 ⋄ 0) = 0 := by
--   rw [unit_unit]
/- Cómo sabría Lean de qué monoide estamos hablando? -/

/-
## Clases
Queda claro que podemos definir de manera análoga el tipo de grupos, anillos,
espacios vectoriales, etc. Pero actualmente es inconveniente usarlos, como vimos
en el último ejemplo.

En vez de considerar el tipo de, por ejemplo, monoides; es mejor considerar el
tipo de estructuras de monoides que un tipo puede tener:
-/
structure MonoidStructure (A : Type) where
  op : A → A → A
  unit : A
  op_assoc (a b c : A) : op (op a b) c = op a (op b c)
  op_unit (a : A) : op a unit = a
  unit_op (a : A) : op unit a = a

def NatMonoidStructure : MonoidStructure ℕ := {
  op a b := a + b
  unit := 0
  op_assoc a b c := by ring
  op_unit a := by ring
  unit_op a := by ring
}

/-
Cómo ayuda esto? Las clases permiten enseñarle a Lean que tenemos una
estructura canónica en cierto tipo.
-/
class Monoid (A : Type) where
  op : A → A → A
  unit : A
  op_assoc (a b c : A) : op (op a b) c = op a (op b c)
  op_unit (a : A) : op a unit = a
  unit_op (a : A) : op unit a = a

instance NatMonoid : Monoid ℕ := {
  op a b := a + b
  unit := 0
  op_assoc a b c := by ring
  op_unit a := by ring
  unit_op a := by ring
}

notation3 x " ⋄' " y => Monoid.op x y
notation3 "𝟘" => Monoid.unit

example : (0 ⋄' 0) = 0 := by
  sorry

lemma unit_unit' (M : Type) [Monoid M] :
  (𝟘 ⋄' 𝟘) = (𝟘 : M) := by
  rw [Monoid.op_unit]


/-
## La jerarquía algebraica de clases

Las estructuras algebraicas comunes (y más!) ya están en Lean.
-/

#check Group
#check Ring
#check UniqueFactorizationMonoid
#check IsPrincipalIdealRing
#check EuclideanDomain
#check Field
#check Module
#check Algebra

#synth Field ℝ
#synth Module ℝ (ℝ × ℝ)
#synth Module ℝ (ℝ → ℝ)

example (k : Type) [Field k] : EuclideanDomain k := inferInstance


/-!
## Ejercicios
Probaremos el primer teorema de isomorfía para grupos.
Sugerencia: Use structuras cuando sea necesario.
-/

variable {G H : Type} [Group G] [Group H]

/- El kernel. -/
def Kernel (f : G →ₙ* H) : Subgroup G := sorry

instance KernelNormal (f : G →ₙ* H) : Subgroup.Normal (Kernel f) := sorry

/- El cociente G/N. Sugerencia: use clases de equivalencia. -/
def Quotient (N : Subgroup G) [h : Subgroup.Normal N] : Type :=
  sorry

instance (N : Subgroup G) [h : Subgroup.Normal N] : Group (Quotient N) :=
  sorry

/- La imagen Im(f). -/
def Image (f : G →ₙ* H) : Type := sorry

instance (f : G →ₙ* H) : Group (Image f) := sorry

/-- Primer teorema de isomorfía. -/
def FirstIso (f : G →ₙ* H) : Quotient (Kernel f) ≅ Image f := sorry

/-


-/
