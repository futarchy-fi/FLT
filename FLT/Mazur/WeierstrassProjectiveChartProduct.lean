/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineProduct
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Integral products of projective Weierstrass charts

These are actual tensor products of the normalized cubic coordinate rings,
including products with a Y = 1 input chart. Their spectra are the scheme
fiber products, and setting either input to infinity gives a retraction onto
the other factor. No addition map on these product charts is assumed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (j k : Fin 3)

/-- Any map out of an integral chart gives a projective solution of the cubic. -/
theorem projective_equation_of_hom (f : Coordinate W j →ₐ[R] S) :
    (W.map (algebraMap R S)).toProjective.Equation (f ∘ coord W j) := by
  have h := (coord_equation W j).map f.toRingHom
  change ((W.map (algebraMap R (Coordinate W j))).map f.toRingHom).toProjective.Equation
    (f ∘ coord W j) at h
  have hf : (W.map (algebraMap R (Coordinate W j))).map f.toRingHom =
      W.map (algebraMap R S) := by
    ext <;> exact f.commutes _
  rw [hf] at h
  exact h

/-- The integral coordinate ring for a pair of arbitrary normalized projective charts. -/
def ChartProduct := Coordinate W j ⊗[R] Coordinate W k

instance : CommRing (ChartProduct W j k) :=
  inferInstanceAs (CommRing (Coordinate W j ⊗[R] Coordinate W k))

instance : Algebra R (ChartProduct W j k) :=
  inferInstanceAs (Algebra R (Coordinate W j ⊗[R] Coordinate W k))

/-- First projection, contravariantly on the coordinate algebras. -/
def chartProductLeft : Coordinate W j →ₐ[R] ChartProduct W j k :=
  Algebra.TensorProduct.includeLeft

/-- Second projection, contravariantly on the coordinate algebras. -/
def chartProductRight : Coordinate W k →ₐ[R] ChartProduct W j k :=
  Algebra.TensorProduct.includeRight

/-- The first universal input satisfies the projective equation after every specialization. -/
theorem chartProductLeft_equation (f : ChartProduct W j k →ₐ[R] S) :
    (W.map (algebraMap R S)).toProjective.Equation
      (fun i => f (chartProductLeft W j k (coord W j i))) :=
  projective_equation_of_hom W j (f.comp (chartProductLeft W j k))

/-- The second universal input satisfies the projective equation after every specialization. -/
theorem chartProductRight_equation (f : ChartProduct W j k →ₐ[R] S) :
    (W.map (algebraMap R S)).toProjective.Equation
      (fun i => f (chartProductRight W j k (coord W k i))) :=
  projective_equation_of_hom W k (f.comp (chartProductRight W j k))

/-- A pair of chart-valued algebra points evaluates on the product. -/
def chartProductEvaluation (f : Coordinate W j →ₐ[R] S) (g : Coordinate W k →ₐ[R] S) :
    ChartProduct W j k →ₐ[R] S :=
  Algebra.TensorProduct.lift f g (fun _ _ => Commute.all ..)

/-- Evaluation restricts to the given first input. -/
@[simp] theorem chartProductEvaluation_left
    (f : Coordinate W j →ₐ[R] S) (g : Coordinate W k →ₐ[R] S) :
    (chartProductEvaluation W j k f g).comp (chartProductLeft W j k) = f :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ _

/-- Evaluation restricts to the given second input. -/
@[simp] theorem chartProductEvaluation_right
    (f : Coordinate W j →ₐ[R] S) (g : Coordinate W k →ₐ[R] S) :
    (chartProductEvaluation W j k f g).comp (chartProductRight W j k) = g :=
  Algebra.TensorProduct.lift_comp_includeRight' _ _ _

/-- Maps from the product are determined by their restrictions to the two factors. -/
theorem chartProduct_hom_ext {f g : ChartProduct W j k →ₐ[R] S}
    (hl : f.comp (chartProductLeft W j k) = g.comp (chartProductLeft W j k))
    (hr : f.comp (chartProductRight W j k) = g.comp (chartProductRight W j k)) : f = g :=
  Algebra.TensorProduct.ext hl hr

/-- Infinity defines an integral point of the Y = 1 chart over every base algebra. -/
def chartInfinityEvaluation : Coordinate W 1 →ₐ[R] S :=
  evaluation W 1 ![0, 1, 0] Projective.equation_zero rfl

/-- The integral infinity point has its expected coordinates. -/
@[simp] theorem chartInfinityEvaluation_coord (i : Fin 3) :
    chartInfinityEvaluation (S := S) W (coord W 1 i) = ![0, 1, 0] i :=
  evaluation_coord W 1 _ _ _ i

/-- Set the first input equal to infinity and keep the second input universal. -/
def chartProductAtLeftInfinity : ChartProduct W 1 k →ₐ[R] Coordinate W k :=
  chartProductEvaluation W 1 k (chartInfinityEvaluation W) (AlgHom.id R _)

/-- Set the second input equal to infinity and keep the first input universal. -/
def chartProductAtRightInfinity : ChartProduct W j 1 →ₐ[R] Coordinate W j :=
  chartProductEvaluation W j 1 (AlgHom.id R _) (chartInfinityEvaluation W)

/-- The zero-section specialization retains the other factor exactly. -/
@[simp] theorem chartProductAtLeftInfinity_right :
    (chartProductAtLeftInfinity W k).comp (chartProductRight W 1 k) = AlgHom.id R _ :=
  chartProductEvaluation_right W 1 k _ _

/-- The opposite zero-section specialization also retains the other factor. -/
@[simp] theorem chartProductAtRightInfinity_left :
    (chartProductAtRightInfinity W j).comp (chartProductLeft W j 1) = AlgHom.id R _ :=
  chartProductEvaluation_left W j 1 _ _

/-- The first factor of the zero section is the actual infinity point. -/
@[simp] theorem chartProductAtLeftInfinity_left :
    (chartProductAtLeftInfinity W k).comp (chartProductLeft W 1 k) =
      chartInfinityEvaluation W :=
  chartProductEvaluation_left W 1 k _ _

/-- The second factor of the opposite zero section is the actual infinity point. -/
@[simp] theorem chartProductAtRightInfinity_right :
    (chartProductAtRightInfinity W j).comp (chartProductRight W j 1) =
      chartInfinityEvaluation W :=
  chartProductEvaluation_right W j 1 _ _

/-- The all-affine instance is the previously constructed affine product algebra. -/
def chartProductAffineEquiv : ChartProduct W 2 2 ≃ₐ[R] AffineProduct W := AlgEquiv.refl

/-- The integral product chart represents the actual fiber product over Spec R. -/
def chartProductSpecIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W j))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W k)))) ≅
      Spec (CommRingCat.of (ChartProduct W j k)) :=
  pullbackSpecIso R (Coordinate W j) (Coordinate W k)

/-- The fiber-product identification carries the first projection to the tensor inclusion. -/
@[reassoc] theorem chartProductSpecIso_inv_fst :
    (chartProductSpecIso W j k).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (chartProductLeft W j k).toRingHom) :=
  pullbackSpecIso_inv_fst R (Coordinate W j) (Coordinate W k)

/-- The fiber-product identification carries the second projection to the tensor inclusion. -/
@[reassoc] theorem chartProductSpecIso_inv_snd :
    (chartProductSpecIso W j k).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (chartProductRight W j k).toRingHom) :=
  pullbackSpecIso_inv_snd R (Coordinate W j) (Coordinate W k)

end FLT.Mazur.WeierstrassIntegralChart
