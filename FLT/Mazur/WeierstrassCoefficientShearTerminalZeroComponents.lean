/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearOriginalTerminalNode
public import FLT.Mazur.WeierstrassCoefficientShearOriginalTerminalConics
import all FLT.Mazur.WeierstrassCoefficientShearOriginalTerminalConics
import all FLT.Mazur.WeierstrassCoefficientShearTerminalNode
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
public import FLT.Mazur.WeierstrassConicCoefficientTransport
public import FLT.Mazur.WeierstrassDilatationResidueBoundaryFunctions
public import FLT.Mazur.WeierstrassDividedTerminalComponents
public import FLT.Mazur.WeierstrassDividedTerminalZeroComponents

/-!
# Complete scale-one terminal components glued from the sheared affine charts

The full preceding conic parameters are glued to the opposite terminal
branches using reciprocal coordinates, including both origins.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
  (hp : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "V" => W.map (residue R)
local notation "hs" => WeierstrassDilatation.residue_scale_eq_zero D (start + (j + 1)) (by omega)
local notation "h3" => Iff.mpr (residue_eq_zero_iff _)
  (And.left (divided_linear_mem D (start + (j + 1)) hk
    (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "h4" => Iff.mpr (residue_eq_zero_iff _)
  (And.right (divided_linear_mem D (start + (j + 1)) hk
    (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "h6" => Iff.mpr (residue_eq_zero_iff _)
  (divided_constant_mem D (start + (j + 1)) hp (Data.b6 d) (Data.factor6 d))
local notation "hr" => show (0 : K) ^ 2 + algebraMap R K W.a₁ * 0 -
    algebraMap R K W.a₂ = 0 from by
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub, neg_eq_zero]
  exact (residue_eq_zero_iff _).mpr D.a₂_mem
local notation "a" => residueTangentUnit D
local notation "ha" => Eq.trans (residueTangentUnit_val D) (Eq.symm (rootShearZero_tangent V))
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "hsPrev" => show algebraMap R K (π ^ (start + j)) = 1 from by
  rw [hk0, pow_zero, map_one]
local notation "hπ₀" => Iff.mpr (residue_eq_zero_iff π)
  (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
local notation "C" => coefficientShearRetainedScaleOneConic hπ data K 0
  j hj 0 hj hsPrev hπ₀ h3 h4 hr
local notation "c" => residue R (Data.b6 d)
local notation "E" => conicZeroAffineIso c h6
local notation "P₁" => (E).hom ≫ coefficientConicFirstParameter
  (rootShearCurve V 0).a₁ c hu C
local notation "P₂" => (E).hom ≫ coefficientConicSecondParameter
  (rootShearCurve V 0).a₁ c hu C
local notation "B₁" => coefficientShearTerminalFirstBranch
  hπ data K 0 (j + 1) hj hs h3 h4 h6 hr a ha
local notation "B₂" => coefficientShearTerminalSecondBranch
  hπ data K 0 (j + 1) hj hs h3 h4 h6 hr a ha
local notation "G" => coefficientShearGluedIso hπ data K 0 (j + 1) hj

/-- The full first conic and opposite terminal branch agree on their reciprocal overlap. -/
theorem coefficientShearTerminalZeroFirstComponent_overlap :
    ProjectiveLine.overlapLeft K ≫ P₁ = ProjectiveLine.overlapRight K ≫ B₂ := by
  apply (cancel_mono (G).hom).mp
  simp only [Category.assoc]
  rw [coefficientShearTerminalZeroFirstParameter_original
      hπ data D j hj hk hπ₀ h3 h4 hr hk0 hsPrev hu,
    coefficientShearTerminalSecondBranch_original
      hπ data D (j + 1) hj (by omega) hk hp]
  exact terminalZeroFirstComponent_overlap hπ data D j hj hk0 hk hp

/-- The complete first component is constructed from its two full coefficient charts. -/
def coefficientShearTerminalZeroFirstComponent :
    ProjectiveLine.scheme K ⟶ coefficientShearGlued hπ data K 0 (j + 1) hj :=
  pushout.desc P₁ B₂
    (coefficientShearTerminalZeroFirstComponent_overlap hπ data D j hj hk0 hk hp)

/-- The left chart retains the entire first conic parameter. -/
@[reassoc] theorem coefficientShearTerminalZeroFirstComponent_left :
    ProjectiveLine.left K ≫ coefficientShearTerminalZeroFirstComponent hπ data D j hj hk0 hk hp =
      P₁ := pushout.inl_desc _ _ _

/-- The right chart retains the complete opposite terminal branch. -/
@[reassoc] theorem coefficientShearTerminalZeroFirstComponent_right :
    ProjectiveLine.right K ≫ coefficientShearTerminalZeroFirstComponent hπ data D j hj hk0 hk hp =
      B₂ := pushout.inr_desc _ _ _

/-- Reconstruction identifies the independently glued full first terminal component. -/
@[reassoc] theorem coefficientShearTerminalZeroFirstComponent_original :
    coefficientShearTerminalZeroFirstComponent hπ data D j hj hk0 hk hp ≫ (G).hom =
      terminalZeroFirstComponent hπ data D j hj hk0 hk hp := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫
        coefficientShearTerminalZeroFirstComponent hπ data D j hj hk0 hk hp ≫ (G).hom =
      ProjectiveLine.left K ≫ terminalZeroFirstComponent hπ data D j hj hk0 hk hp
    rw [coefficientShearTerminalZeroFirstComponent_left_assoc, terminalZeroFirstComponent_left]
    apply congrArg ((E).hom ≫ ·)
    exact coefficientShearTerminalZeroFirstParameter_original
      hπ data D j hj hk hπ₀ h3 h4 hr hk0 hsPrev hu
  · change ProjectiveLine.right K ≫
        coefficientShearTerminalZeroFirstComponent hπ data D j hj hk0 hk hp ≫ (G).hom =
      ProjectiveLine.right K ≫ terminalZeroFirstComponent hπ data D j hj hk0 hk hp
    rw [coefficientShearTerminalZeroFirstComponent_right_assoc, terminalZeroFirstComponent_right]
    exact coefficientShearTerminalSecondBranch_original
      hπ data D (j + 1) hj (by omega) hk hp

/-- The full second conic and opposite terminal branch agree on their reciprocal overlap. -/
theorem coefficientShearTerminalZeroSecondComponent_overlap :
    ProjectiveLine.overlapLeft K ≫ P₂ = ProjectiveLine.overlapRight K ≫ B₁ := by
  apply (cancel_mono (G).hom).mp
  simp only [Category.assoc]
  rw [coefficientShearTerminalZeroSecondParameter_original
      hπ data D j hj hk hπ₀ h3 h4 hr hk0 hsPrev hu,
    coefficientShearTerminalFirstBranch_original
      hπ data D (j + 1) hj (by omega) hk hp]
  exact terminalZeroSecondComponent_overlap hπ data D j hj hk0 hk hp

/-- The complete second component is constructed from its two full coefficient charts. -/
def coefficientShearTerminalZeroSecondComponent :
    ProjectiveLine.scheme K ⟶ coefficientShearGlued hπ data K 0 (j + 1) hj :=
  pushout.desc P₂ B₁
    (coefficientShearTerminalZeroSecondComponent_overlap hπ data D j hj hk0 hk hp)

/-- The left chart retains the entire second conic parameter. -/
@[reassoc] theorem coefficientShearTerminalZeroSecondComponent_left :
    ProjectiveLine.left K ≫ coefficientShearTerminalZeroSecondComponent hπ data D j hj hk0 hk hp =
      P₂ := pushout.inl_desc _ _ _

/-- The right chart retains the complete opposite terminal branch. -/
@[reassoc] theorem coefficientShearTerminalZeroSecondComponent_right :
    ProjectiveLine.right K ≫ coefficientShearTerminalZeroSecondComponent hπ data D j hj hk0 hk hp =
      B₁ := pushout.inr_desc _ _ _

/-- Reconstruction identifies the independently glued full second terminal component. -/
@[reassoc] theorem coefficientShearTerminalZeroSecondComponent_original :
    coefficientShearTerminalZeroSecondComponent hπ data D j hj hk0 hk hp ≫ (G).hom =
      terminalZeroSecondComponent hπ data D j hj hk0 hk hp := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫
        coefficientShearTerminalZeroSecondComponent hπ data D j hj hk0 hk hp ≫ (G).hom =
      ProjectiveLine.left K ≫ terminalZeroSecondComponent hπ data D j hj hk0 hk hp
    rw [coefficientShearTerminalZeroSecondComponent_left_assoc, terminalZeroSecondComponent_left]
    apply congrArg ((E).hom ≫ ·)
    exact coefficientShearTerminalZeroSecondParameter_original
      hπ data D j hj hk hπ₀ h3 h4 hr hk0 hsPrev hu
  · change ProjectiveLine.right K ≫
        coefficientShearTerminalZeroSecondComponent hπ data D j hj hk0 hk hp ≫ (G).hom =
      ProjectiveLine.right K ≫ terminalZeroSecondComponent hπ data D j hj hk0 hk hp
    rw [coefficientShearTerminalZeroSecondComponent_right_assoc, terminalZeroSecondComponent_right]
    exact coefficientShearTerminalFirstBranch_original
      hπ data D (j + 1) hj (by omega) hk hp

end FLT.Mazur.WeierstrassDividedDepth
