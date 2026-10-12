/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNodalZeroLaterComponents
import all FLT.Mazur.WeierstrassNodalZeroLaterComponents
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneGluedIntersections
public import FLT.Mazur.WeierstrassNodalZeroRetainedComponents
import all FLT.Mazur.WeierstrassNodalZeroRetainedChart
public import FLT.Mazur.WeierstrassCoefficientShearSpecializationMono

/-!
# Both actual first adjacent intersections at start depth zero

The entire first retained conic uses its genuine scale-one equation. Both
signed next-line intersections persist in the integral tangent model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {depth n : ℕ}
  (hbound : 2 * (0 + n) ≤ depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (hc : IsUnit W.c₄)
  (m : ℕ) (ht : 2 + m ≤ n)
local notation "data" => nodalDepthFamily hm hbound h3 h4 h6
local notation "d" => data (Fin.mk 1 (by omega))
local notation "e" => data (Fin.mk 2 (by omega))
local notation "Q" => AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "a" => IsUnit.unit (nodalDepth_tangent_a₁_isUnit h3 h4 hc)
local notation "ha" => IsUnit.unit_spec (nodalDepth_tangent_a₁_isUnit h3 h4 hc)
local notation "c" => algebraMap R Q (Data.b6 d)
local notation "g0" => nodalDepth_tangent_scale_zeroDepth (W := W) (π := π)
local notation "gp" => residueTangentEquation_zero W π
  (Iff.mp (residue_eq_zero_iff π) (nodalDepth_residue_uniformizer hm))
local notation "g3" => And.left
  (nodalDepthFamily_tangent_linear_zero hm hbound h3 h4 h6 hπ (Fin.mk 2 (by omega)))
local notation "g4" => And.right
  (nodalDepthFamily_tangent_linear_zero hm hbound h3 h4 h6 hπ (Fin.mk 2 (by omega)))
local notation "gc" => And.right (And.right (coefficientShearAdjacent_coefficients hπ d e Q gp))
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (WeierstrassCurve.a₁ U) c)
local notation "p" => Spec.map (CommRingCat.ofHom
  (Polynomial.toLaurent : Polynomial Q →+* Q[T;T⁻¹]))
local notation "C" => nodalDepthZeroRetainedConic hπ hm hbound h3 h4 h6
  (2 + m) ht (by omega)
local notation "L" => nodalDepthZeroLaterLine hπ hm hbound h3 h4 h6
  (2 + m) ht (Fin.mk 1 (by omega)) Nat.zero_lt_one
local notation "gd3" => And.left (coefficientShearAdjacent_coefficients hπ d e Q gp)
local notation "gd4" => And.left (And.right (coefficientShearAdjacent_coefficients hπ d e Q gp))
local notation "hr" => residueTangentEquation_root W
local notation "TC" => tensorShearScaleOneConicImmersion W (π ^ 0) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r g0 gp gd3 gd4 hr
local notation "old" => coefficientShearRetainedTensorChart hπ data Q r
  (2 + m) ht (Fin.mk 0 (by omega))
local notation "special" => coefficientShearTangentSpecialization hπ data (2 + m) ht

set_option maxHeartbeats 600000 in
-- Original and normalized tensor charts require additional elaboration heartbeats.
/-- The scale-one tensor conic reconstructs the whole actual first retained conic. -/
theorem nodalDepthZeroFirstConic_tensor : (TC ≫ old) ≫ special = C := by
  let E := tensorShearScaleOneFiberEquiv W (π ^ 0) π
    (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r g0 gp gd3 gd4 hr
  let F := coefficientShearScaleOneFiberEquiv W (π ^ 0) π
    (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r g0 gp gd3 gd4 hr
  let I := successiveCoefficientShearIso W (π ^ 0) π
    (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r
  have h : (Scheme.Spec.mapIso E.toRingEquiv.toCommRingCatIso.op).hom =
      (Scheme.Spec.mapIso F.toRingEquiv.toCommRingCatIso.op).hom ≫ I.hom := by
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  rw [tensorShearScaleOneConicImmersion]
  change ((fiberConicImmersion (WeierstrassCurve.a₁ U) c ≫
    (Scheme.Spec.mapIso E.toRingEquiv.toCommRingCatIso.op).hom) ≫ old) ≫ special = C
  rw [h, coefficientShearRetainedTensorChart]
  simp only [Category.assoc, I, Iso.hom_inv_id_assoc]
  rfl

local notation "b₁" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundaryFirst U c hu gc)))
local notation "ρ₁" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso
    (AlgEquiv.toRingEquiv (PolygonScaledReciprocal.equiv (a⁻¹)))))

set_option maxHeartbeats 600000 in
-- Actual nodal indices require additional elaboration heartbeats.
/-- The full first conic meets the next first line in the signed Laurent puncture. -/
theorem nodalDepthZeroFirstAdjacentFirst_isPullback :
    IsPullback (b₁ ≫ inc) ((ρ₁).hom ≫ p) C (L 0 (middle_first_root U)) := by
  have sq := coefficientShearScaleOneAdjacentGluedFirstFull_isPullback hπ data Q r
    0 (by omega) (by omega) m ht g0 gp g3 g4 hr a ha
  have result : IsPullback (b₁ ≫ inc) ((ρ₁).hom ≫ p)
      ((TC ≫ old) ≫ special) (L 0 (middle_first_root U)) :=
    IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ special sq.cone sq.isLimit)
  rw [nodalDepthZeroFirstConic_tensor] at result
  exact result

local notation "b₂" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundarySecond U c hu gc)))
local notation "ρ₂" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso
    (AlgEquiv.toRingEquiv (PolygonScaledReciprocal.equiv ((-a)⁻¹)))))

set_option maxHeartbeats 600000 in
-- Actual nodal indices require additional elaboration heartbeats.
/-- The same full first conic has the opposite signed intersection with the second line. -/
theorem nodalDepthZeroFirstAdjacentSecond_isPullback :
    IsPullback (b₂ ≫ inc) ((ρ₂).hom ≫ p) C
      (L (-WeierstrassCurve.a₁ U) (middle_second_root U)) := by
  have sq := coefficientShearScaleOneAdjacentGluedSecondFull_isPullback hπ data Q r
    0 (by omega) (by omega) m ht g0 gp g3 g4 hr a ha
  have result : IsPullback (b₂ ≫ inc) ((ρ₂).hom ≫ p)
      ((TC ≫ old) ≫ special) (L (-WeierstrassCurve.a₁ U) (middle_second_root U)) :=
    IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ special sq.cone sq.isLimit)
  rw [nodalDepthZeroFirstConic_tensor] at result
  exact result

end FLT.Mazur.WeierstrassDividedDepth
