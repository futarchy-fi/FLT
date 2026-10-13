/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorAffine
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorAffine

/-!
# Both exterior markings at the original zero start

The whole affine normalization identifies both original conic junctions,
including the scale-one equality case with nonzero divided constant.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open ProjectiveLine WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (hj : 1 ≤ n) (m : ℕ) (hm : 0 + 1 + m ≤ n) (hres : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
local notation "d" => data ⟨1, Nat.lt_succ_of_le hj⟩
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
  (h3 : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (data ⟨1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (data ⟨1, Nat.lt_succ_of_le hj⟩).b4 = 0)
local notation "hp" => residueTangentEquation_zero W π ((residue_eq_zero_iff π).mp hres)
local notation "hs" => show algebraMap R Q (π ^ (0 + 0)) = 1 from by simp
local notation "hr" => residueTangentEquation_root W
local notation "L" => coefficientShearRetainedScaleOneIncidence
  hπ data Q r 0 hj m hm hs hp h3 h4 hr
local notation "p" => coefficientShearGluedProjection hπ data Q r (0 + 1 + m) hm
local notation "N" => originalResidueFiniteNormalization
  hπ data (0 + 1 + m) hm d (by dsimp; omega) hres

variable (a : (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))ˣ)
local notation "F" => coefficientShearResidueExteriorLift
  hπ data (0 + 1 + m) hm d (by dsimp; omega) hres a

variable (ha : (a : AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) =
  (nodeTangentShear (W.map (residue R))).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "C₀" => coefficientShearRetainedScaleOneConic
  hπ data Q r 0 hj m hm hs hp h3 h4 hr

/-- The original exterior zero meets the original scale-one first conic marking. -/
@[reassoc] theorem coefficientShearResidueZeroExteriorLift_zero :
    zero Q ≫ F =
      Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint (U).a₁ c hu).toRingHom) ≫ C₀ := by
  rw [← slopeNormalization_first a, infinitySlopeMark, Category.assoc, Category.assoc,
    coefficientShearResidueZeroExteriorLift_affine hπ data hj m hm hres h3 h4 a,
    coefficientShearRetainedScaleOneIncidence_first]

/-- The original exterior infinity meets the opposite scale-one conic marking. -/
@[reassoc] theorem coefficientShearResidueZeroExteriorLift_infinity :
    infinity Q ≫ F =
      Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint (U).a₁ c hu).toRingHom) ≫ C₀ := by
  rw [← slopeNormalization_second a, infinitySlopeMark, Category.assoc, Category.assoc,
    coefficientShearResidueZeroExteriorLift_affine hπ data hj m hm hres h3 h4 a]
  rw [show -(a : Q) = -(U).a₁ from congrArg Neg.neg ha]
  exact coefficientShearRetainedScaleOneIncidence_second
    hπ data Q r 0 hj m hm hs hp h3 h4 hr hu

end FLT.Mazur.WeierstrassDividedDepth
