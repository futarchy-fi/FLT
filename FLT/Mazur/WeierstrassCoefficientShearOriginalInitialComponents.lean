/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialComponents
import all FLT.Mazur.WeierstrassCoefficientShearInitialComponents
public import FLT.Mazur.WeierstrassDividedInitialComponentStructure
public import FLT.Mazur.WeierstrassCoefficientShearOriginalRetainedLines
public import FLT.Mazur.WeierstrassDividedInitialProjectiveComponents
import all FLT.Mazur.WeierstrassCoefficientShearOriginalRetainedLines
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# Original reconstruction and endpoints of complete sheared initial components

Both independently glued components recover the original full projective maps,
including their initial and retained node markings and coefficient structures.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (h1 : 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + 1) ≤ depth)
  (m : ℕ) (hm : 1 + m ≤ n)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
local notation "V" => W.map (residue R)
local notation "U" => rootShearCurve V 0
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D start (by omega) (Data.b6 d) (Data.factor6 d))
local notation "hs" => WeierstrassDilatation.residue_scale_eq_zero D start hstart
local notation "hp" => Iff.mpr (residue_eq_zero_iff π)
  (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
local notation "g3" => Iff.mpr (residue_eq_zero_iff _)
  (And.left (WeierstrassDilatation.divided_linear_mem
    D start (by omega) (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "g4" => Iff.mpr (residue_eq_zero_iff _)
  (And.right (WeierstrassDilatation.divided_linear_mem
    D start (by omega) (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "h3" => Iff.mpr (residue_eq_zero_iff _)
  (And.left (WeierstrassDilatation.divided_linear_mem
    D (start + 1) hk (Data.b3 e) (Data.b4 e) (Data.factor3 e) (Data.factor4 e)))
local notation "h4" => Iff.mpr (residue_eq_zero_iff _)
  (And.right (WeierstrassDilatation.divided_linear_mem
    D (start + 1) hk (Data.b3 e) (Data.b4 e) (Data.factor3 e) (Data.factor4 e)))
local notation "hr" => show (0 : K) ^ 2 + algebraMap R K W.a₁ * 0 -
    algebraMap R K W.a₂ = 0 from by
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub, neg_eq_zero]
  exact (residue_eq_zero_iff _).mpr D.a₂_mem
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "ha" => Eq.trans (WeierstrassDilatation.residueTangentUnit_val D)
  (Eq.symm (rootShearZero_tangent V))
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "conic" => coefficientShearInitialConic hπ data K 0 (1 + m) hm hs g3 g4 hr
local notation "E" => conicZeroAffineIso c hc
local notation "F₁" => (E).hom ≫ coefficientConicFirstParameter (U).a₁ c hu conic
local notation "F₂" => (E).hom ≫ coefficientConicSecondParameter (U).a₁ c hu conic
local notation "line" => coefficientShearRetainedLine hπ data K 0 (1 + m) hm
  (Fin.mk 0 (by omega)) hs hp h3 h4 hr
local notation "L₁" => line 0 (middle_first_root U)
local notation "L₂" => line (-(U).a₁) (middle_second_root U)
local notation "G" => coefficientShearGluedIso hπ data K 0 (1 + m) hm


/-- The complete first coefficient component reconstructs the original initial component. -/
@[reassoc] theorem coefficientShearInitialFirstComponent_original :
    coefficientShearInitialFirstComponent hπ data D h1 hstart hk m hm ≫ (G).hom =
      initialGlobalFirstComponent hπ data D h1 hstart hk m hm := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫
        coefficientShearInitialFirstComponent hπ data D h1 hstart hk m hm ≫ (G).hom =
      ProjectiveLine.left K ≫ initialGlobalFirstComponent hπ data D h1 hstart hk m hm
    rw [initialGlobalFirstComponent_left,
      coefficientShearInitialFirstComponent_left_assoc]
    apply congrArg ((E).hom ≫ ·)
    exact coefficientShearInitialFirstParameter_original
      hπ data D (1 + m) hm hstart (by omega) hs g3 g4 hr hu
  · change ProjectiveLine.right K ≫
        coefficientShearInitialFirstComponent hπ data D h1 hstart hk m hm ≫ (G).hom =
      ProjectiveLine.right K ≫ initialGlobalFirstComponent hπ data D h1 hstart hk m hm
    rw [initialGlobalFirstComponent_right,
      coefficientShearInitialFirstComponent_right_assoc]
    apply congrArg (ProjectiveLine.chartScaling K a⁻¹ ≫ ·)
    exact coefficientShearRetainedFirst_original
      hπ data D 0 h1 m hm hstart hk hs hp h3 h4 hr

/-- The full first initial component preserves the residue-field structure. -/
@[reassoc] theorem coefficientShearInitialFirstComponent_structure :
    coefficientShearInitialFirstComponent hπ data D h1 hstart hk m hm ≫
        coefficientShearGluedStructure hπ data K 0 (1 + m) hm =
      ProjectiveLine.toBase K := by
  change _ ≫ (G).hom ≫ _ = _
  rw [← Category.assoc, coefficientShearInitialFirstComponent_original,
    initialGlobalFirstComponent_structure]

/-- The first zero marking reconstructs the actual original initial node. -/
@[reassoc] theorem coefficientShearInitialFirstComponent_zero_original :
    ProjectiveLine.zero K ≫
        coefficientShearInitialFirstComponent hπ data D h1 hstart hk m hm ≫ (G).hom =
      initialGlobalFirstSection hπ data D (1 + m) hm hstart (by omega) := by
  rw [coefficientShearInitialFirstComponent_original, initialGlobalFirstComponent_zero]

/-- The first infinity reconstructs the actual first retained node. -/
@[reassoc] theorem coefficientShearInitialFirstComponent_infinity_original :
    ProjectiveLine.infinity K ≫
        coefficientShearInitialFirstComponent hπ data D h1 hstart hk m hm ≫ (G).hom =
      olderGlobalFirstSection hπ data D 0 h1 m hm hstart hk := by
  rw [coefficientShearInitialFirstComponent_original, initialGlobalFirstComponent_infinity]

/-- The complete second coefficient component reconstructs the original initial component. -/
@[reassoc] theorem coefficientShearInitialSecondComponent_original :
    coefficientShearInitialSecondComponent hπ data D h1 hstart hk m hm ≫ (G).hom =
      initialGlobalSecondComponent hπ data D h1 hstart hk m hm := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫
        coefficientShearInitialSecondComponent hπ data D h1 hstart hk m hm ≫ (G).hom =
      ProjectiveLine.left K ≫ initialGlobalSecondComponent hπ data D h1 hstart hk m hm
    rw [initialGlobalSecondComponent_left,
      coefficientShearInitialSecondComponent_left_assoc]
    apply congrArg ((E).hom ≫ ·)
    exact coefficientShearInitialSecondParameter_original
      hπ data D (1 + m) hm hstart (by omega) hs g3 g4 hr hu
  · change ProjectiveLine.right K ≫
        coefficientShearInitialSecondComponent hπ data D h1 hstart hk m hm ≫ (G).hom =
      ProjectiveLine.right K ≫ initialGlobalSecondComponent hπ data D h1 hstart hk m hm
    rw [initialGlobalSecondComponent_right,
      coefficientShearInitialSecondComponent_right_assoc]
    apply congrArg (ProjectiveLine.chartScaling K (-a)⁻¹ ≫ ·)
    exact coefficientShearRetainedSecond_original
      hπ data D 0 h1 m hm hstart hk hs hp h3 h4 hr

/-- The full second initial component preserves the residue-field structure. -/
@[reassoc] theorem coefficientShearInitialSecondComponent_structure :
    coefficientShearInitialSecondComponent hπ data D h1 hstart hk m hm ≫
        coefficientShearGluedStructure hπ data K 0 (1 + m) hm =
      ProjectiveLine.toBase K := by
  change _ ≫ (G).hom ≫ _ = _
  rw [← Category.assoc, coefficientShearInitialSecondComponent_original,
    initialGlobalSecondComponent_structure]

/-- The second zero marking reconstructs the actual original initial node. -/
@[reassoc] theorem coefficientShearInitialSecondComponent_zero_original :
    ProjectiveLine.zero K ≫
        coefficientShearInitialSecondComponent hπ data D h1 hstart hk m hm ≫ (G).hom =
      initialGlobalSecondSection hπ data D (1 + m) hm hstart (by omega) := by
  rw [coefficientShearInitialSecondComponent_original, initialGlobalSecondComponent_zero]

/-- The second infinity reconstructs the actual first retained node. -/
@[reassoc] theorem coefficientShearInitialSecondComponent_infinity_original :
    ProjectiveLine.infinity K ≫
        coefficientShearInitialSecondComponent hπ data D h1 hstart hk m hm ≫ (G).hom =
      olderGlobalSecondSection hπ data D 0 h1 m hm hstart hk := by
  rw [coefficientShearInitialSecondComponent_original, initialGlobalSecondComponent_infinity]

end FLT.Mazur.WeierstrassDividedDepth
