/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalIncidenceUnits

/-!
# A named integral source for the original horizontal action

The secant and output quotient localization is retained as a named ring.
Its original input and genuine action output give algebra maps from the
same horizontal fraction chart, before specialization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassModificationReesCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (d : WeierstrassDividedDepth.Data W π k)
local notation "S" => SmoothHorizontalProductRing W (π ^ k)
local notation "a" => smoothHorizontalLeft W (π ^ k)
local notation "c" => smoothHorizontalRight W (π ^ k)
local notation "p" => smoothHorizontalPoint W (π ^ k)
local notation "ha" => smoothHorizontalLeft_inclusion W (π ^ k)
local notation "hp" => smoothHorizontal_structure W (π ^ k)
local notation "ψ" => smoothHorizontalInput W (π ^ k)
local notation "hc" => smoothHorizontalRight_contraction W (π ^ k)
local notation "hf" => smoothHorizontalInput_flat W (π ^ k)
local notation "T" => SecantPairRing W a c
local notation "α" => AlgHom.toRingHom
  (AlgHom.comp (secantPairPresentation W a c) (ordinaryChartAddition W false))
local notation "β" => AlgHom.toRingHom (AlgHom.comp (IsScalarTower.toAlgHom R S T) c)
local notation "p'" => Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ p
/-- The actual secant and horizontal-output refinement of the integral product. -/
def SmoothHorizontalActionRing := LeftSmoothFractionActionOpen W (π ^ k) d.b3 d.b4 (π ^ k * d.b6)
  d.factor3 d.factor4 (smoothHorizontal_factor6 d) p' α β
  (secantPairSmooth_structure W a c p hp) (secantPairSmooth_addition W a c p ha hp)
  (coord W 2 0) (centerGenerators_mem W (π ^ k) 1)
  (secantHorizontalInput W (π ^ k) a c ψ) (secantHorizontal_beta W π a c ψ hc) 1

local notation "O" => SmoothHorizontalActionRing d

instance smoothHorizontalActionRingCommRing : CommRing O := by
  unfold SmoothHorizontalActionRing
  infer_instance

instance smoothHorizontalActionRingAlgebra : Algebra R O := by
  unfold SmoothHorizontalActionRing
  infer_instance

instance smoothHorizontalActionRingSourceAlgebra : Algebra S O := by
  unfold SmoothHorizontalActionRing
  infer_instance

instance smoothHorizontalActionRingSourceTower : IsScalarTower R S O := by
  unfold SmoothHorizontalActionRing
  infer_instance

instance smoothHorizontalActionRingSecantAlgebra : Algebra T O := by
  unfold SmoothHorizontalActionRing
  infer_instance

instance smoothHorizontalActionRingSecantTower : IsScalarTower S T O := by
  unfold SmoothHorizontalActionRing
  infer_instance

/-- The common secant and horizontal-output refinement is flat over the original product. -/
theorem smoothHorizontalActionRing_source_flat : RingHom.Flat (algebraMap S O) := by
  rw [IsScalarTower.algebraMap_eq S T O]
  apply (secantPair_restriction_flat W a c).comp
  apply RingHom.flat_algebraMap_iff.mpr
  unfold SmoothHorizontalActionRing
  infer_instance

local notation "H" => HorizontalSourceRing W (π ^ k)

/-- The original horizontal input on the actual integral output refinement. -/
def smoothHorizontalIntegralInput : H →ₐ[R] O :=
  (IsScalarTower.toAlgHom R S O).comp (IsScalarTower.toAlgHom R H S)

/-- The genuine horizontal action output, with its proved coefficient compatibility. -/
def smoothHorizontalIntegralOutput : H →ₐ[R] O :=
  { smoothHorizontalActionLift d with
    commutes' := smoothHorizontalActionLift_coefficient d }

/-- The named input retains every original horizontal fraction function. -/
@[simp] theorem smoothHorizontalIntegralInput_apply (q : H) :
    smoothHorizontalIntegralInput d q = algebraMap S O (smoothHorizontalInput W (π ^ k) q) :=
  rfl

/-- The named output is the original integral action lift on every function. -/
@[simp] theorem smoothHorizontalIntegralOutput_apply (q : H) :
    smoothHorizontalIntegralOutput d q = smoothHorizontalActionLift d q := rfl

/-- The retained original horizontal input remains flat on the integral action refinement. -/
theorem smoothHorizontalIntegralInput_flat :
    RingHom.Flat (smoothHorizontalIntegralInput d).toRingHom := by
  exact (smoothHorizontalInput_flat W (π ^ k)).comp
    (smoothHorizontalActionRing_source_flat d)

variable [IsDomain R] [IsLocalRing R] {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hk0 : 0 < k) (hk : 2 * k < depth) (hπ : π ≠ 0)
local notation "C" => SmoothHorizontalResidueRing D
local notation "e₁" => smoothHorizontalFirstResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
local notation "e₂" => smoothHorizontalSecondResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
local notation "E₁" => smoothHorizontalFirstOutputResidue D d hk0 hk hπ
local notation "E₂" => smoothHorizontalSecondOutputResidue D d hk0 hk hπ

/-- The first original residue on the named integral action source. -/
def smoothHorizontalIntegralFirstResidue : O →ₐ[R] C :=
  { E₁ with
    commutes' := fun r => by
      change E₁ (algebraMap R O r) = algebraMap R C r
      rw [IsScalarTower.algebraMap_apply R S O]
      exact (smoothHorizontalFirstOutputResidue_base D d hk0 hk hπ
        (algebraMap R S r)).trans ((e₁).commutes r) }

/-- The opposite original residue on the same integral action source. -/
def smoothHorizontalIntegralSecondResidue : O →ₐ[R] C :=
  { E₂ with
    commutes' := fun r => by
      change E₂ (algebraMap R O r) = algebraMap R C r
      rw [IsScalarTower.algebraMap_apply R S O]
      exact (smoothHorizontalSecondOutputResidue_base D d hk0 hk hπ
        (algebraMap R S r)).trans ((e₂).commutes r) }

/-- Every original product function survives the named first residue specialization. -/
theorem smoothHorizontalIntegralFirstResidue_base (q : S) :
    smoothHorizontalIntegralFirstResidue d D hk0 hk hπ (algebraMap S O q) = e₁ q :=
  smoothHorizontalFirstOutputResidue_base D d hk0 hk hπ q

/-- Every original product function survives the opposite residue specialization. -/
theorem smoothHorizontalIntegralSecondResidue_base (q : S) :
    smoothHorizontalIntegralSecondResidue d D hk0 hk hπ (algebraMap S O q) = e₂ q :=
  smoothHorizontalSecondOutputResidue_base D d hk0 hk hπ q

/-- Both first-branch incidence images are units on the original action source. -/
theorem smoothHorizontalIntegralFirstResidue_units :
    IsUnit (smoothHorizontalIntegralFirstResidue d D hk0 hk hπ
      (smoothHorizontalIntegralInput d (horizontalScale W (π ^ k)))) ∧
    IsUnit (smoothHorizontalIntegralFirstResidue d D hk0 hk hπ
      (smoothHorizontalIntegralOutput d (horizontalScale W (π ^ k)))) := by
  constructor
  · rw [smoothHorizontalIntegralInput_apply, smoothHorizontalIntegralFirstResidue_base]
    exact smoothHorizontalFirstResidue_incidence_unit D d hk0 hk hπ
  · exact smoothHorizontalFirstOutputResidue_incidence_unit D d hk0 hk hπ

/-- Both opposite-branch incidence images are units on the same original action source. -/
theorem smoothHorizontalIntegralSecondResidue_units :
    IsUnit (smoothHorizontalIntegralSecondResidue d D hk0 hk hπ
      (smoothHorizontalIntegralInput d (horizontalScale W (π ^ k)))) ∧
    IsUnit (smoothHorizontalIntegralSecondResidue d D hk0 hk hπ
      (smoothHorizontalIntegralOutput d (horizontalScale W (π ^ k)))) := by
  constructor
  · rw [smoothHorizontalIntegralInput_apply, smoothHorizontalIntegralSecondResidue_base]
    exact smoothHorizontalSecondResidue_incidence_unit D d hk0 hk hπ
  · exact smoothHorizontalSecondOutputResidue_incidence_unit D d hk0 hk hπ

end FLT.Mazur.WeierstrassIntegralChart
