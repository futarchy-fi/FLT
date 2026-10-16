/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstSourcePoleCubic
public import FLT.Mazur.PolygonSmoothingNodeDenominatorCoverage

/-!
# Complete cubic Z coverage of the full original source-node quotient

Every ideal containing the two original scaled
source coordinates gives a full quotient covered by complete cubic Z
patches. There is no target-coordinate or target-denominator hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentFirstStageParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "b" => ringMap (stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1)
  (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit K)

local notation "s" => completeIdentityFirstPoleSource K n h U
local notation "d" => nodeMarkingDenominator (t)
local notation "A" => Γ((R), (V).1)
local notation "Z" => CompleteIdentityFirstSourcePolePatch K n h U
local notation "ι" => algebraMap (A) (Z)
local notation "M" => completeIdentityFirstSourcePolePatchMap K n h U
local notation "κ" => completeIdentityActionAdicChartSpaceMap K n h 1 0 0 ≫
  completeIdentityActionAdicLiftSpaceMap K n h 1
variable (I : Ideal Γ(completeIdentityActionAdicChartSpace K n h 1 0 0,
  (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U).1))
variable (hx : completeIdentityFirstPoleSource K n h U (leftCoordinate (parameter K 1)) ∈ I)
variable (hy : completeIdentityFirstPoleSource K n h U (rightCoordinate (parameter K 1)) ∈ I)
local notation "q" => Ideal.Quotient.mk I

include hx

/-- The source-node ideal already contains the actual original smoothing parameter. -/
theorem completeIdentityFirstSourceNodeQuotient_parameter :
    (ρ) (completeIdentityFirstAmbientParameter K n h) ∈ I := by
  have he : (s) (leftCoordinate (t)) * (s) (rightCoordinate (t)) =
      (ρ) (completeIdentityFirstAmbientParameter K n h) := by
    rw [← (s).map_mul, coordinate_relation]
    change (ρ) ((completeIdentityFirstAmbientSourceFunctions K n h)
      ((σ) ((b) (algebraMap (Ring K 1) (ChartRing (t)) (t))))) = _
    rw [ringMap_scalar, AlgHom.commutes, stageCoefficientMap_parameter]
    rfl
  rw [← he]
  exact I.mul_mem_right _ hx

include hy

/-- Every full source-node quotient factors through the source-only pole localization. -/
def completeIdentityFirstSourceNodeQuotientLift : (Z) →+* (A) ⧸ I :=
  IsLocalization.Away.lift ((s) (d)) (g := (q)) (by
    rw [nodeMarkingDenominator_quotient_eq_one (t) (s) I hx hy]
    exact isUnit_one)
local notation "φ" => completeIdentityFirstSourceNodeQuotientLift K n h U I hx hy

/-- The lift retains the entire original quotient homomorphism. -/
theorem completeIdentityFirstSourceNodeQuotientLift_algebraMap (z : A) :
    (φ) ((ι) z) = (q) z := IsLocalization.Away.lift_eq _ _ _

/-- The source-only factorization is the original scheme map of the full node quotient. -/
theorem completeIdentityFirstSourceNodeQuotientLift_map :
    Spec.map (CommRingCat.ofHom (φ)) ≫ (M) =
      AffineOpenSpectrumFunctions.map (V) (CommRingCat.ofHom (q)) := by
  rw [completeIdentityFirstSourcePolePatchMap, AffineOpenSpectrumFunctions.map,
    ← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact completeIdentityFirstSourceNodeQuotientLift_algebraMap K n h U I hx hy

/-- The full original parameter/source-node quotient lies in the complete cubic Z open. -/
theorem completeIdentityFirstSourceNodeQuotient_mem_cubicZ
    (z : Spec (.of ((A) ⧸ I))) :
    (κ) ((V).1.ι (AffineOpenSpectrumFunctions.map (V) (CommRingCat.ofHom (q)) z)) ∈
      completeIdentityCubicChartOpen K n h 2 := by
  have hp : (φ) (completeIdentityFirstSourcePoleParameter K n h U) = 0 := by
    rw [completeIdentityFirstSourcePoleParameter,
      completeIdentityFirstSourceNodeQuotientLift_algebraMap]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (completeIdentityFirstSourceNodeQuotient_parameter K n h U I hx)
  have hz := completeIdentityFirstSourcePole_mem_cubicZ K n h U (φ) hp z
  have he := congrArg (fun f ↦ f z)
    (completeIdentityFirstSourceNodeQuotientLift_map K n h U I hx hy)
  change (M) ((Spec.map (CommRingCat.ofHom (φ))) z) = _ at he
  rw [he] at hz
  exact hz

/-- Every point of that unchanged quotient has a complete affine Z-compatible refinement. -/
theorem completeIdentityFirstSourceNodeQuotient_cubicZ_refinement
    (z : Spec (.of ((A) ⧸ I))) :
    ∃ W : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens,
      (V).1.ι (AffineOpenSpectrumFunctions.map (V) (CommRingCat.ofHom (q)) z) ∈
        (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 W).1 ∧
      (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 W).1 ≤
        completeIdentityCubicChartOpen K n h 2 ∧
      (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 W).1 ≤
        completeIdentityAdicNodeNeighborhood K n h 1 0 0 :=
  completeIdentityAdicCubicPatch_at K n h 1 0 0 _ 2
    (completeIdentityFirstSourceNodeQuotient_mem_cubicZ K n h U I hx hy z)

end FLT.Mazur.PolygonInfinitesimalStages
