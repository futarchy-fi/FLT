/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic

/-!
# The infinity chart of a Weierstrass cubic

This is the actual affine hypersurface obtained by setting Y = 1 in the
homogeneous Weierstrass equation, over an arbitrary commutative base ring.
It includes its structural map, the section (X/Y,Z/Y) = (0,0), and the
polynomial identity needed to glue it to the ordinary affine chart.
No projective gluing, group scheme, or modular curve is asserted here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace WeierstrassCurve.InfinityChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The equation in coordinates u = X/Y, v = Z/Y. -/
def equation : MvPolynomial (Fin 2) R :=
  X 1 + C W.a₁ * X 0 * X 1 + C W.a₃ * X 1 ^ 2 -
    (X 0 ^ 3 + C W.a₂ * X 0 ^ 2 * X 1 +
      C W.a₄ * X 0 * X 1 ^ 2 + C W.a₆ * X 1 ^ 3)

/-- This equation is the dehomogenization of the existing projective cubic. -/
theorem equation_eq_dehomogenization :
    equation W = eval₂Hom C ![X 0, 1, X 1] W.toProjective.polynomial := by
  simp [equation, Projective.polynomial]

/-- The coordinate ring of the chart, with its defining equation imposed. -/
abbrev CoordinateRing :=
  MvPolynomial (Fin 2) R ⧸ Ideal.span {equation W}

/-- The chart is a genuine affine scheme. -/
def scheme : Scheme.{u} := Spec (.of (CoordinateRing W))

/-- Its closed embedding in the affine plane. -/
def inclusion : scheme W ⟶ Spec (.of (MvPolynomial (Fin 2) R)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {equation W})))

instance inclusion_isClosedImmersion : IsClosedImmersion (inclusion W) := by
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- Projection to the coefficient base. -/
def toBase : scheme W ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing W)))

/-- Evaluation at the origin of this chart. -/
def origin : CoordinateRing W →ₐ[R] R :=
  Ideal.Quotient.liftₐ (Ideal.span {equation W}) (aeval (fun _ ↦ 0)) (by
    change Ideal.span {equation W} ≤ RingHom.ker (aeval (fun _ : Fin 2 ↦ (0 : R))).toRingHom
    rw [Ideal.span_le]
    intro f hf
    rcases Set.mem_singleton_iff.mp hf with rfl
    simp [equation])

/-- The section represented in homogeneous coordinates by [0:1:0]. -/
def infinity : Spec (.of R) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (origin W).toRingHom)

@[reassoc (attr := simp)]
theorem infinity_toBase : infinity W ≫ toBase W = 𝟙 _ := by
  unfold infinity toBase scheme
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext r
  exact (origin W).commutes r

/-- The derivative in the v direction is a unit at the section, over every
base ring, including residue characteristics two and three. -/
theorem derivative_at_origin :
    eval (fun _ ↦ 0) (pderiv 1 (equation W)) = 1 := by
  simp [equation]

/-- On the overlap with the ordinary affine chart, u = x/y and v = 1/y.
The formula is valid over arbitrary rings whenever y has the specified inverse. -/
theorem transition_equation (x y t : R) (ht : t * y = 1) :
    eval ![x * t, t] (equation W) =
      t ^ 3 * (y ^ 2 + W.a₁ * x * y + W.a₃ * y -
        (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) := by
  simp only [equation, map_sub, map_add, map_mul, map_pow,
    eval_X, eval_C, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination -(t + t ^ 2 * y + W.a₁ * x * t ^ 2 + W.a₃ * t ^ 2) * ht

section Points

variable {S : Type*} [CommRing S] [Algebra R S]

/-- Every solution of the infinity-chart equation over an R-algebra gives
an actual R-algebra map from its coordinate ring. -/
def point (v : Fin 2 → S) (hv : aeval v (equation W) = 0) :
    CoordinateRing W →ₐ[R] S :=
  Ideal.Quotient.liftₐ (Ideal.span {equation W}) (aeval v) (by
    change Ideal.span {equation W} ≤ RingHom.ker (aeval v).toRingHom
    rw [Ideal.span_le]
    intro f hf
    rcases Set.mem_singleton_iff.mp hf with rfl
    exact hv)

/-- Evaluation has the specified coordinates. -/
@[simp] theorem point_coordinate (v : Fin 2 → S)
    (hv : aeval v (equation W) = 0) (i : Fin 2) :
    point W v hv (Ideal.Quotient.mk _ (X i)) = v i := by
  change aeval v (X i) = v i
  simp

/-- Maps out of this chart ring are determined by the two affine coordinates. -/
@[ext] theorem hom_ext {f g : CoordinateRing W →ₐ[R] S}
    (h : ∀ i, f (Ideal.Quotient.mk _ (X i)) =
      g (Ideal.Quotient.mk _ (X i))) : f = g := by
  apply Ideal.Quotient.algHom_ext
  ext i
  exact h i

/-- Solutions are represented uniquely by the concrete chart ring. -/
theorem existsUnique_point (v : Fin 2 → S) (hv : aeval v (equation W) = 0) :
    ∃! f : CoordinateRing W →ₐ[R] S,
      ∀ i, f (Ideal.Quotient.mk _ (X i)) = v i := by
  refine ⟨point W v hv, point_coordinate W v hv, ?_⟩
  intro f hf
  apply hom_ext W
  intro i
  rw [hf, point_coordinate]

end Points

end WeierstrassCurve.InfinityChart
