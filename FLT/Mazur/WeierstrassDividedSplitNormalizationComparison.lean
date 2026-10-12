/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedIncidenceNormalization
public import FLT.Mazur.WeierstrassDividedResidueNormalization
public import FLT.Mazur.WeierstrassDividedProjectiveLift
public import FLT.Mazur.WeierstrassIntegralCoefficientMap
public import FLT.Mazur.WeierstrassSplitCompleteNormalization

/-!
# The actual split exterior is the unique complete normalization lift

Compare the constructed proper extension with the original complete incidence
component by all affine cubic coordinates. The result retains its coefficient
projection and applies at every original finite modification stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth) (hdepth : 0 < depth)
local notation "K" => ResidueField R
local notation "V" => W.map (algebraMap R K)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "g" => finiteGlobalStructure hπ data j hj
local notation "f" => initialProjectiveToGlobal hπ data D j hj hstart hk hdepth
local notation "c" => finiteGlobalContraction hπ data j hj

include data D hstart in
omit [IsBezout R] [IsDomain R] in
/-- The actual split residue cubic has all four required zero coefficients. -/
theorem initialSplitNormalization_coefficients :
    (V).a₂ = 0 ∧ (V).a₃ = 0 ∧ (V).a₄ = 0 ∧ (V).a₆ = 0 := by
  refine ⟨(residue_eq_zero_iff W.a₂).mpr D.a₂_mem, ?_⟩
  exact originalResidue_normalization_coefficients d hstart
    ((residue_eq_zero_iff π).mpr (by
      rw [D.maximalIdeal_eq]
      exact Ideal.subset_span (Set.mem_singleton π)))

local notation "h" => initialSplitNormalization_coefficients data D hstart
local notation "s" => splitNormalizationChart V (h).1 (h).2.1 (h).2.2.1 (h).2.2.2

omit [IsBezout R] in
/-- The split normalization retains every function of the actual original incidence chart. -/
theorem initialIncidenceNormalization_eq_split :
    initialIncidenceNormalization data D hstart hk =
      ((s).restrictScalars R).comp (chartCoefficientMap (S := K) W 2) := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply]
    rw [chartCoefficientMap_coord, splitNormalizationChart_coord]
    exact initialIncidenceNormalization_x data D hstart hk
  · rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply]
    rw [chartCoefficientMap_coord, splitNormalizationChart_coord]
    exact initialIncidenceNormalization_y data D hstart hk
  · change initialIncidenceNormalization data D hstart hk (coord W 2 2) =
      (((s).restrictScalars R).comp (chartCoefficientMap (S := K) W 2)) (coord W 2 2)
    rw [coord_self, map_one, map_one]

/-- The complete split normalization still targets the original integral cubic. -/
def initialSplitCompleteNormalization : scheme K ⟶ integralCurve W :=
  splitCompleteNormalization V (h).1 (h).2.1 (h).2.2.1 (h).2.2.2 ≫
    integralCoefficientMorphism (S := K) W

omit [IsBezout R] [IsDomain R] in
/-- The complete split normalization preserves its actual integral residue projection. -/
@[reassoc] theorem initialSplitCompleteNormalization_base :
    initialSplitCompleteNormalization data D hstart ≫ integralCurveStructure W =
      toBase K ≫ q := by
  rw [initialSplitCompleteNormalization, Category.assoc, integralCoefficientMorphism_structure]
  erw [splitCompleteNormalization_base_assoc]

omit [IsBezout R] in
/-- The entire original affine incidence map is the restriction of the complete normalization. -/
@[reassoc] theorem initialSplitCompleteNormalization_left :
    left K ≫ initialSplitCompleteNormalization data D hstart =
      Spec.map (CommRingCat.ofHom
        (initialIncidenceNormalization data D hstart hk).toRingHom) ≫ integralCurveChart W 2 := by
  rw [initialSplitCompleteNormalization, splitCompleteNormalization_left_assoc,
    splitAffineToCubic, Category.assoc]
  erw [integralCurveChart_coefficientMorphism]
  rw [initialIncidenceNormalization_eq_split]
  change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
  rw [← Spec.map_comp_assoc]
  rfl

/-- The complete original incidence component projects to the constructed split normalization. -/
@[reassoc] theorem initialProjectiveToGlobal_contraction :
    f ≫ pullback.snd q g ≫ c = initialSplitCompleteNormalization data D hstart := by
  refine ext_of_isDominant_of_isSeparated (integralCurveStructure W) ?_ (left K) ?_
  · rw [Category.assoc, Category.assoc, ← finiteGlobalStructure,
      ← pullback.condition, ← Category.assoc]
    have hf : f ≫ pullback.fst q g = toBase K := by
      rw [initialProjectiveToGlobal, Category.assoc, ← initialExteriorStructure,
        ← initialExteriorProjectiveIso_structure hπ data D j hj hstart hk hdepth,
        Iso.inv_hom_id_assoc]
    rw [hf, initialSplitCompleteNormalization_base]
  · rw [initialProjectiveToGlobal_affine_contraction,
      initialSplitCompleteNormalization_left data D hstart hk]

/-- The proper lift is the actual complete split component, not an assumed comparison. -/
theorem initialProjectiveToGlobal_eq_lift :
    f ≫ pullback.snd q g =
      projectiveFiniteLift hπ data j hj
        (initialIncidenceNormalization data D hstart hk).toRingHom
        (initialIncidenceNormalization_x_regular data D hstart hk)
        (initialSplitCompleteNormalization data D hstart)
        (initialSplitCompleteNormalization_left data D hstart hk) := by
  apply projectiveFiniteLift_unique hπ data j hj
    (initialIncidenceNormalization data D hstart hk).toRingHom
    (initialIncidenceNormalization_x_regular data D hstart hk)
    (initialSplitCompleteNormalization data D hstart)
    (initialSplitCompleteNormalization_left data D hstart hk)
  · exact initialProjectiveToGlobal_contraction hπ data D j hj hstart hk hdepth
  · exact projectiveFiniteLift_contraction _ _ _ _ _ _ _ _

end FLT.Mazur.WeierstrassDividedDepth
