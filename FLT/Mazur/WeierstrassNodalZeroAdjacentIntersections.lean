/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNodalZeroLaterComponents
import all FLT.Mazur.WeierstrassNodalZeroLaterComponents
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
public import FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedIntersections
public import FLT.Mazur.WeierstrassCoefficientShearSpecializationMono

/-!
# Full later adjacent intersections when the original family starts at zero

Positive retained indices supply the vanishing scale without requiring a
positive start depth. Both signed full intersections persist in the actual
integral tangent model through its monic coefficient specialization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {depth n : ℕ}
  (hbound : 2 * (0 + n) ≤ depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (hc : IsUnit W.c₄)
  (j m : ℕ) (ht : j + 2 + m ≤ n) (hpos : 0 < j)
local notation "data" => nodalDepthFamily hm hbound h3 h4 h6
local notation "d" => data (Fin.mk (j + 1) (by omega))
local notation "e" => data (Fin.mk (j + 2) (by omega))
local notation "Q" => AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "a" => IsUnit.unit (nodalDepth_tangent_a₁_isUnit h3 h4 hc)
local notation "ha" => IsUnit.unit_spec (nodalDepth_tangent_a₁_isUnit h3 h4 hc)
local notation "c" => algebraMap R Q (Data.b6 d)
local notation "g0" => nodalDepth_tangent_scale_zero (W := W) hm
  (by omega : 0 < 0 + j)
local notation "gp" => residueTangentEquation_zero W π
  (Iff.mp (residue_eq_zero_iff π) (nodalDepth_residue_uniformizer hm))
local notation "g3" => And.left
  (nodalDepthFamily_tangent_linear_zero hm hbound h3 h4 h6 hπ (Fin.mk (j + 2) (by omega)))
local notation "g4" => And.right
  (nodalDepthFamily_tangent_linear_zero hm hbound h3 h4 h6 hπ (Fin.mk (j + 2) (by omega)))
local notation "gc" => And.right (And.right (coefficientShearAdjacent_coefficients hπ d e Q gp))
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (WeierstrassCurve.a₁ U) c)
local notation "p" => Spec.map (CommRingCat.ofHom
  (Polynomial.toLaurent : Polynomial Q →+* Q[T;T⁻¹]))
local notation "C" => nodalDepthZeroLaterConic hπ hm hbound h3 h4 h6
  (j + 2 + m) ht (Fin.mk j (by omega)) hpos
local notation "L" => nodalDepthZeroLaterLine hπ hm hbound h3 h4 h6
  (j + 2 + m) ht (Fin.mk (j + 1) (by omega)) (Nat.zero_lt_succ j)

local notation "b₁" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundaryFirst U c hu gc)))
local notation "ρ₁" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso
    (AlgEquiv.toRingEquiv (PolygonScaledReciprocal.equiv (a⁻¹)))))

/-- The constructed nonsplit conic has the full first signed intersection in the integral model. -/
theorem nodalDepthZeroLaterAdjacentFirst_isPullback :
    IsPullback (b₁ ≫ inc) ((ρ₁).hom ≫ p) C (L 0 (middle_first_root U)) := by
  have sq := coefficientShearAdjacentGluedFirstFull_isPullback hπ data Q r
    j (by omega) (by omega) m ht g0 gp g3 g4 (residueTangentEquation_root W) a ha
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _
    (coefficientShearTangentSpecialization hπ data (j + 2 + m) ht) sq.cone sq.isLimit)

local notation "b₂" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundarySecond U c hu gc)))
local notation "ρ₂" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso
    (AlgEquiv.toRingEquiv (PolygonScaledReciprocal.equiv ((-a)⁻¹)))))

/-- The constructed nonsplit conic has the full second signed intersection in the integral model. -/
theorem nodalDepthZeroLaterAdjacentSecond_isPullback :
    IsPullback (b₂ ≫ inc) ((ρ₂).hom ≫ p) C (L (-(U).a₁) (middle_second_root U)) := by
  have sq := coefficientShearAdjacentGluedSecondFull_isPullback hπ data Q r
    j (by omega) (by omega) m ht g0 gp g3 g4 (residueTangentEquation_root W) a ha
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _
    (coefficientShearTangentSpecialization hπ data (j + 2 + m) ht) sq.cone sq.isLimit)

end FLT.Mazur.WeierstrassDividedDepth
