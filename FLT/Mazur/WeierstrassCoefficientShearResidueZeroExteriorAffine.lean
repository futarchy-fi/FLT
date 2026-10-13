/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneIncidence
public import FLT.Mazur.WeierstrassSuccessiveShearScaleOneIncidenceContraction
public import FLT.Mazur.WeierstrassCoefficientShearResidueExteriorLift
public import FLT.Mazur.WeierstrassDividedOlderCubicAction
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneIncidence

/-!
# The entire exterior affine line at the original zero start

The full retained scale-one incidence line is the affine restriction of the
proper exterior lift, including both original conic junctions.
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

/-- The entire scale-one incidence line is the affine normalization in the finite model. -/
@[reassoc] theorem coefficientShearResidueZeroIncidence_finiteProjection :
    L ≫ p = left Q ≫ N := by
  apply finiteGlobalContraction_ext_of_regular_x hπ data (0 + 1 + m) hm
    (originalResidueNormalization d (by dsimp; omega) hres)
    (originalResidueNormalization_x_regular d (by dsimp; omega) hres)
  · rw [coefficientShearRetainedScaleOneIncidence_projection, Category.assoc]
    change _ ≫ olderGlobalChart hπ data 0 hj m hm ≫ _ = _
    rw [olderGlobalChart_cubic, ← Spec.map_comp_assoc]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q) ≫
      WeierstrassIntegralChart.integralCurveChart W 2)
      (originalShearScaleOneIncidenceMap_eq_residue d hres h3 h4)
  · rw [Category.assoc, originalResidueFiniteNormalization_contraction,
      originalResidueCompleteNormalization_left]
    rfl

variable (a : (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))ˣ)
local notation "F" => coefficientShearResidueExteriorLift
  hπ data (0 + 1 + m) hm d (by dsimp; omega) hres a

/-- The complete start-zero exterior has its actual full retained scale-one affine parameter. -/
@[reassoc] theorem coefficientShearResidueZeroExteriorLift_affine :
    left Q ≫ (slopeNormalizationIso a).hom ≫ F = L := by
  apply (coefficientShearGlued_isPullback hπ data Q r (0 + 1 + m) hm).hom_ext
  · simp only [Category.assoc]
    rw [coefficientShearResidueExteriorLift_structure,
      slopeNormalizationIso_base, left_toBase,
      coefficientShearRetainedScaleOneIncidence_structure]
  · simp only [Category.assoc]
    rw [coefficientShearResidueExteriorLift_projection,
      coefficientShearResidueOrderedFinite, Iso.hom_inv_id_assoc,
      coefficientShearResidueZeroIncidence_finiteProjection hπ data hj m hm hres h3 h4]

end FLT.Mazur.WeierstrassDividedDepth
