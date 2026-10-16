/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXZeroIdealBoundary
public import FLT.Mazur.NodalFiberUnitScalingBoundary
public import FLT.Mazur.PolygonSmoothingOverlapGraph

/-!
# A genuine full initial polygon comparison on the zero fiber

Constant tangent-unit scaling is an open immersion on the whole initial
neighborhood. Over the zero arithmetic ideal it matches the original Laurent
incidence exactly, without replacing the entire first coordinate by t.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (u : Rˣ)
local notation "N" => NodalFiber.Coordinate (0 : R)
local notation "L" => PolynomialNodeOpen W 0

/-- Scale the full first coordinate by a constant tangent unit on the original zero fiber. -/
def zeroInitialPolygonChart : Spec (.of L) ⟶ PolygonSmoothing.chart R 0 :=
  Spec.map (CommRingCat.ofHom (algebraMap N L)) ≫
    (NodalFiber.unitSmoothingIso 0 0 u (by simp)).hom

/-- This constant normalization is an open immersion on the entire original neighborhood. -/
instance zeroInitialPolygonChart_isOpenImmersion :
    IsOpenImmersion (zeroInitialPolygonChart W u) := by
  let _ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap N L))) :=
    IsOpenImmersion.of_isLocalization (NodalFiber.q 0 + algebraMap R N W.a₁)
  exact IsOpenImmersion.comp _ _

/-- The constant normalized full initial chart preserves its coefficient ring. -/
@[reassoc] theorem zeroInitialPolygonChart_structure :
    zeroInitialPolygonChart W u ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (PolygonSmoothing.ChartRing (0 : R)))) =
        Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
  rw [zeroInitialPolygonChart, Category.assoc, NodalFiber.unitSmoothingIso_structure,
    ← Spec.map_comp]
  rfl

variable (b3 b4 b6 : R) (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
  (hbot : I = ⊥) (hu : (u : R) = W.a₁)
local notation "G" => laurentNodeRestriction W 0 b3 b4 b6 I hI ha (I.zero_mem) h2 h3 h4 h6
local notation "E" => AlgHom.comp (G) (Algebra.algHom R N L)

include hbot hu

/-- Constant normalization removes precisely the zero-fiber boundary correction. -/
theorem zeroInitialPolygon_normalizedEvaluation :
    NodalFiber.unitNormalizedEvaluation 0 0 u (by simp) E =
      LaurentPolynomial.invert.toAlgHom.comp (PolygonSmoothing.leftLaurentMap (0 : R)) := by
  apply PolygonSmoothing.chartRing_hom_ext 0
  · rw [NodalFiber.unitNormalizedEvaluation_left]
    change algebraMap R R[T;T⁻¹] (↑u⁻¹ : R) * G (algebraMap N L (NodalFiber.p 0)) = _
    rw [laurentNodeRestriction_p_of_bot W 0 b3 b4 b6 I hI ha (I.zero_mem)
      h2 h3 h4 h6 hbot, ← hu, ← LaurentPolynomial.C_eq_algebraMap,
      mul_left_comm, ← map_mul, Units.inv_mul, map_one, mul_one]
    simp
  · rw [NodalFiber.unitNormalizedEvaluation_right]
    change G (algebraMap N L (NodalFiber.q 0)) = _
    rw [laurentNodeRestriction_q_of_bot W 0 b3 b4 b6 I hI ha (I.zero_mem)
      h2 h3 h4 h6 hbot]
    simp

/-- The genuine full open immersion has the required original inverse Laurent parameter. -/
@[reassoc] theorem zeroInitialPolygonChart_boundary :
    Spec.map (CommRingCat.ofHom (G).toRingHom) ≫ zeroInitialPolygonChart W u =
      (PolygonSmoothing.edgeInversion R).hom ≫ PolygonSmoothing.leftBranchOpen R 0 := by
  rw [zeroInitialPolygonChart, ← Category.assoc, ← Spec.map_comp,
    PolygonSmoothing.leftBranchOpen_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f.toRingHom))
    (zeroInitialPolygon_normalizedEvaluation W u b3 b4 b6 I hI ha h2 h3 h4 h6 hbot hu)

end FLT.Mazur.WeierstrassModificationX
