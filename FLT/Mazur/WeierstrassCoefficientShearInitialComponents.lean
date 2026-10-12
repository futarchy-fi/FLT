/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearOriginalInitialConic
public import FLT.Mazur.WeierstrassCoefficientShearOriginalRetainedLines
public import FLT.Mazur.WeierstrassDividedInitialProjectiveComponents
import all FLT.Mazur.WeierstrassCoefficientShearOriginalRetainedLines
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# Complete initial components from the actual sheared affine charts

Glue the full initial conic parameters to the first retained lines in the
root-zero coefficient model. The original signed reciprocal overlaps prove
that these independently specified affine charts form projective components.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
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

/-- The full first conic parameter and first retained line have the original overlap. -/
theorem coefficientShearInitialFirstComponent_overlap :
    ProjectiveLine.overlapLeft K ≫ F₁ =
      Spec.map (CommRingCat.ofHom
        (PolygonScaledReciprocal.reciprocal a⁻¹).toRingHom) ≫
          ProjectiveLine.overlapLeft K ≫ L₁ := by
  apply (cancel_mono (G).hom).mp
  simp only [Category.assoc]
  rw [coefficientShearInitialFirstParameter_original
      hπ data D (1 + m) hm hstart (by omega) hs g3 g4 hr hu,
    coefficientShearRetainedFirst_original
      hπ data D 0 h1 m hm hstart hk hs hp h3 h4 hr]
  exact initialGlobalFirstComponent_overlap hπ data D h1 hstart hk m hm

/-- The complete first initial component, glued from actual coefficient charts. -/
def coefficientShearInitialFirstComponent :
    ProjectiveLine.scheme K ⟶ coefficientShearGlued hπ data K 0 (1 + m) hm :=
  ProjectiveLine.scaledReciprocalDesc a⁻¹ F₁ L₁
    (coefficientShearInitialFirstComponent_overlap hπ data D h1 hstart hk m hm)

/-- The entire original first conic parameter is retained by the left chart. -/
@[reassoc] theorem coefficientShearInitialFirstComponent_left :
    ProjectiveLine.left K ≫
      coefficientShearInitialFirstComponent hπ data D h1 hstart hk m hm = F₁ :=
  ProjectiveLine.scaledReciprocalDesc_left _ _ _ _

/-- The right chart retains the full first line with its signed reciprocal scale. -/
@[reassoc] theorem coefficientShearInitialFirstComponent_right :
    ProjectiveLine.right K ≫
        coefficientShearInitialFirstComponent hπ data D h1 hstart hk m hm =
      ProjectiveLine.chartScaling K a⁻¹ ≫ L₁ :=
  ProjectiveLine.scaledReciprocalDesc_right _ _ _ _

/-- The full second conic parameter and first retained line have the original overlap. -/
theorem coefficientShearInitialSecondComponent_overlap :
    ProjectiveLine.overlapLeft K ≫ F₂ =
      Spec.map (CommRingCat.ofHom
        (PolygonScaledReciprocal.reciprocal (-a)⁻¹).toRingHom) ≫
          ProjectiveLine.overlapLeft K ≫ L₂ := by
  apply (cancel_mono (G).hom).mp
  simp only [Category.assoc]
  rw [coefficientShearInitialSecondParameter_original
      hπ data D (1 + m) hm hstart (by omega) hs g3 g4 hr hu,
    coefficientShearRetainedSecond_original
      hπ data D 0 h1 m hm hstart hk hs hp h3 h4 hr]
  exact initialGlobalSecondComponent_overlap hπ data D h1 hstart hk m hm

/-- The complete second initial component, glued from actual coefficient charts. -/
def coefficientShearInitialSecondComponent :
    ProjectiveLine.scheme K ⟶ coefficientShearGlued hπ data K 0 (1 + m) hm :=
  ProjectiveLine.scaledReciprocalDesc (-a)⁻¹ F₂ L₂
    (coefficientShearInitialSecondComponent_overlap hπ data D h1 hstart hk m hm)

/-- The entire original second conic parameter is retained by the left chart. -/
@[reassoc] theorem coefficientShearInitialSecondComponent_left :
    ProjectiveLine.left K ≫
      coefficientShearInitialSecondComponent hπ data D h1 hstart hk m hm = F₂ :=
  ProjectiveLine.scaledReciprocalDesc_left _ _ _ _

/-- The right chart retains the full second line with its signed reciprocal scale. -/
@[reassoc] theorem coefficientShearInitialSecondComponent_right :
    ProjectiveLine.right K ≫
        coefficientShearInitialSecondComponent hπ data D h1 hstart hk m hm =
      ProjectiveLine.chartScaling K (-a)⁻¹ ≫ L₂ :=
  ProjectiveLine.scaledReciprocalDesc_right _ _ _ _

end FLT.Mazur.WeierstrassDividedDepth
