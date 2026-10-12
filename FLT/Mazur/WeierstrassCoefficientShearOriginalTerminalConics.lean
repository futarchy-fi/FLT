/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveResidueConicShearComparison
public import FLT.Mazur.WeierstrassCoefficientShearRetainedReconstruction
public import FLT.Mazur.WeierstrassDividedTerminalParameterOrigins
public import FLT.Mazur.WeierstrassIncidenceCoefficientTransport
public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
public import FLT.Mazur.WeierstrassCoefficientShearInitialFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# Full preceding conics and parameters in the original terminal model

Both positive-scale and scale-one conics reconstruct the entire original
immersions. Their complete affine parameters preserve the ordered origins.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "V" => W.map (residue R)
local notation "U" => rootShearCurve V 0
variable (hp : algebraMap R (ResidueField R) π = 0)
  (h3 : algebraMap R (ResidueField R) (data ⟨j + 1, by omega⟩).b3 = 0)
  (h4 : algebraMap R (ResidueField R) (data ⟨j + 1, by omega⟩).b4 = 0)
  (hr : (0 : ResidueField R) ^ 2 + algebraMap R (ResidueField R) W.a₁ * 0 -
    algebraMap R (ResidueField R) W.a₂ = 0)
local notation "c" => residue R (Data.b6 d)
local notation "H" => conicCoefficientTransport c (Eq.symm (rootShearZero_tangent V))
local notation "E" => coefficientShearGluedIso hπ data K 0 (j + 1) hj

/-- The final retained tensor chart reconstructs its actual current global chart. -/
@[reassoc] theorem coefficientShearTerminalRetainedTensor_original :
    coefficientShearRetainedTensorChart hπ data K 0 (j + 1) hj ⟨j, Nat.lt_succ_self j⟩ ≫ (E).hom =
      globalSuccessiveTensorChart hπ data K j hj := by
  rw [coefficientShearRetainedTensorChart_original hπ data K 0 j hj 0 hj,
    olderGlobalTensorChart_zero_retention]

section Positive
variable (hk0 : 0 < start + j)
  (hs : algebraMap R (ResidueField R) (π ^ (start + j)) = 0)
local notation "C" => coefficientShearRetainedConic hπ data K 0
  (j + 1) hj ⟨j, Nat.lt_succ_self j⟩ hs hp h3 h4 hr

/-- Reconstruction preserves the entire positive-scale conic immersion. -/
theorem coefficientShearTerminalConic_original :
    C ≫ (E).hom = Spec.map (CommRingCat.ofHom (H).toAlgHom.toRingHom) ≫
      residueSuccessiveConicImmersion D (start + j) hk0 hk
        (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) ≫
          globalSuccessiveTensorChart hπ data K j hj := by
  rw [← coefficientShearRetainedTensorChart_conic, Category.assoc,
    coefficientShearTerminalRetainedTensor_original]
  rw [← residueSuccessiveConicImmersion_eq_shear D hk d hp h3 h4 hr hk0 hs,
    Category.assoc]

variable (hu : IsUnit (rootShearCurve (W.map (residue R)) 0).a₁)

/-- The full first parameter reconstructs its actual original terminal conic map. -/
@[reassoc] theorem coefficientShearTerminalFirstParameter_original :
    coefficientConicFirstParameter (U).a₁ c hu C ≫ (E).hom =
      terminalConicFirstParameter hπ data D j hj hk0 hk := by
  rw [coefficientConicFirstParameter, Category.assoc, Category.assoc,
    coefficientShearTerminalConic_original hπ data D j hj hk hp h3 h4 hr hk0 hs,
    conicFirstParameter_coefficientTransport_assoc c _ (residue_tangent_isUnit D) hu]
  rfl

/-- The full second parameter reconstructs its actual original terminal conic map. -/
@[reassoc] theorem coefficientShearTerminalSecondParameter_original :
    coefficientConicSecondParameter (U).a₁ c hu C ≫ (E).hom =
      terminalConicSecondParameter hπ data D j hj hk0 hk := by
  rw [coefficientConicSecondParameter, Category.assoc, Category.assoc,
    coefficientShearTerminalConic_original hπ data D j hj hk hp h3 h4 hr hk0 hs,
    conicSecondParameter_coefficientTransport_assoc c _ (residue_tangent_isUnit D) hu]
  rfl

end Positive

section ScaleOne
variable (hk0 : start + j = 0)
  (hs : algebraMap R (ResidueField R) (π ^ (start + j)) = 1)
local notation "C" => coefficientShearRetainedScaleOneConic hπ data K 0
  j hj 0 hj hs hp h3 h4 hr

/-- Reconstruction preserves the entire scale-one conic immersion. -/
@[reassoc] theorem coefficientShearTerminalZeroConic_original :
    C ≫ (E).hom = Spec.map (CommRingCat.ofHom (H).toAlgHom.toRingHom) ≫
      zeroResidueConicImmersion D (start + j) hk0 hk
        (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) ≫
          globalSuccessiveTensorChart hπ data K j hj := by
  rw [coefficientShearRetainedScaleOneConic, Category.assoc,
    coefficientShearTerminalRetainedTensor_original]
  rw [← zeroResidueConicImmersion_eq_shear D hk d hp h3 h4 hr hk0 hs,
    Category.assoc]

variable (hu : IsUnit (rootShearCurve (W.map (residue R)) 0).a₁)

/-- The full first parameter reconstructs its actual original terminal conic map. -/
@[reassoc] theorem coefficientShearTerminalZeroFirstParameter_original :
    coefficientConicFirstParameter (U).a₁ c hu C ≫ (E).hom =
      terminalZeroConicFirstParameter hπ data D j hj hk0 hk := by
  rw [coefficientConicFirstParameter, Category.assoc, Category.assoc,
    coefficientShearTerminalZeroConic_original hπ data D j hj hk hp h3 h4 hr hk0 hs,
    conicFirstParameter_coefficientTransport_assoc c _ (residue_tangent_isUnit D) hu]
  rfl

/-- The full second parameter reconstructs its actual original terminal conic map. -/
@[reassoc] theorem coefficientShearTerminalZeroSecondParameter_original :
    coefficientConicSecondParameter (U).a₁ c hu C ≫ (E).hom =
      terminalZeroConicSecondParameter hπ data D j hj hk0 hk := by
  rw [coefficientConicSecondParameter, Category.assoc, Category.assoc,
    coefficientShearTerminalZeroConic_original hπ data D j hj hk hp h3 h4 hr hk0 hs,
    conicSecondParameter_coefficientTransport_assoc c _ (residue_tangent_isUnit D) hu]
  rfl

end ScaleOne

end FLT.Mazur.WeierstrassDividedDepth
