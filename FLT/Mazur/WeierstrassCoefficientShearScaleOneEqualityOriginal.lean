/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOneEqualityComponent
public import FLT.Mazur.WeierstrassCoefficientShearOriginalTerminalLaurent
public import FLT.Mazur.WeierstrassDividedEqualityComponentEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearGluedOverIso
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper
public import FLT.Mazur.ProjectiveLineValuationExtension
public import FLT.Mazur.ProjectiveLineOpenChartExclusion

/-!
# Original comparison for the independent scale-one equality terminal

At preceding scale one, the root-zero construction is the exact
original equality-terminal map. Agreement of the entire Laurent charts
extends over both endpoints by the proved separatedness of the target.
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
  (hp : 2 * (start + j + 1) = depth)
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
local notation "hc" => (divided_constant_isUnit D (start + (j + 1)) hp
  (Data.b6 d) (Data.factor6 d)).map (residue R)
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
local notation "C" => coefficientShearScaleOneEqualityComponent
  hπ data K 0 j hj hsPrev hπ₀ h3 h4 hc hr a ha
local notation "G" => coefficientShearGluedIso hπ data K 0 (j + 1) hj
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (j + 1) hj)
local notation "O" => laurentTerminalProjectiveComponent hπ data D j hj hk hp

/-- The independent full Laurent chart is the original equality-depth chart. -/
@[reassoc] theorem coefficientShearScaleOneEqualityComponent_original_torus :
    ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫ C ≫ (G).hom =
      ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫ O := by
  rw [coefficientShearScaleOneEqualityComponent_torus_assoc,
    coefficientShearTerminalLaurent_original,
    laurentTerminalProjectiveComponent_torus]

/-- The entire projective comparison recovers the original map at its original final stage. -/
@[reassoc] theorem coefficientShearScaleOneEqualityComponent_original : C ≫ (G).hom = O := by
  let _ : IsSeparated (finiteGlobalStructure hπ data (j + 1) hj) :=
    (finiteGlobalStructure_isProper hπ data (j + 1) hj).toIsSeparated
  let _ : IsSeparated p := by infer_instance
  let _ : IsDominant (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) :=
    ⟨ProjectiveLine.openChart_denseRange K _⟩
  refine ext_of_isDominant_of_isSeparated p ?_
    (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ?_
  · rw [Category.assoc]
    change C ≫ coefficientShearGluedStructure hπ data K 0 (j + 1) hj = O ≫ p
    rw [coefficientShearScaleOneEqualityComponent_structure,
      laurentTerminalProjectiveComponent_structure]
  · simpa only [Category.assoc] using
      coefficientShearScaleOneEqualityComponent_original_torus hπ data D j hj hk0 hk hp

/-- The independent map recovers the exact original over-category component. -/
theorem coefficientShearScaleOneEqualityOverComponent_original :
    coefficientShearScaleOneEqualityOverComponent
        hπ data K 0 j hj hsPrev hπ₀ h3 h4 hc hr a ha ≫
      (coefficientShearGluedOverIso hπ data K 0 (j + 1) hj).hom =
        equalityTerminalOverComponent hπ data D j hj hk hp := by
  apply Over.OverMorphism.ext
  exact coefficientShearScaleOneEqualityComponent_original hπ data D j hj hk0 hk hp

end FLT.Mazur.WeierstrassDividedDepth
