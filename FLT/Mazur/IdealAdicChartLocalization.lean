/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineChartSectionLocalization
public import FLT.Mazur.DirectSumLocalization
public import FLT.Mazur.IdealAdicGradedRestriction

/-!
# Localization of the original graded coefficients over each affine chart

All ideal-adic degrees localize together at any chart scalar. The maps and
scalar actions are the original restrictions and degree-zero inclusions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.IdealAdicQuotient
open scoped DirectSum

universe u

namespace FLT.Mazur.IdealAdicGradedSections

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
variable (V : X.affineOpens)

/-- All original coefficient degrees, with scalars restricted from the given affine chart. -/
abbrev chartTotal (W : X.Opens) (h : W ≤ V.1) : ModuleCat Γ(X, V.1) :=
  ModuleCat.of Γ(X, V.1)
    (⨁ n : ℕ, AffineChartSectionLocalization.sections (idealGraded I n) V W h)

/-- The direct sum of the original chart-linear homogeneous restrictions. -/
def chartTotalRestriction {W T : X.Opens} (hW : W ≤ V.1) (hT : T ≤ V.1) (i : W ⟶ T) :
    chartTotal I V T hT →ₗ[Γ(X, V.1)] chartTotal I V W hW :=
  DirectSum.lmap (fun n ↦
    AffineChartSectionLocalization.restriction (idealGraded I n) V hW hT i)

/-- The chart-linear map retains the original multiplicative coefficient restriction. -/
lemma chartTotalRestriction_apply {W T : X.Opens} (hW : W ≤ V.1) (hT : T ≤ V.1)
    (i : W ⟶ T) (s : Sections I T) :
    chartTotalRestriction I V hW hT i s = restrictRingHom I W i s := by
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add s t hs ht => simp only [map_add, hs, ht]
  | of n s =>
    exact (DirectSum.lmap_of (fun k ↦
      AffineChartSectionLocalization.restriction (idealGraded I k) V hW hT i) n s).trans
      (restrict_of I W i n s).symm

/-- All actual degrees localize at each principal refinement of their original affine chart. -/
lemma chartTotalRestriction_isLocalized (r : Γ(X, V.1)) :
    IsLocalizedModule.Away r (chartTotalRestriction I V (X.basicOpen_le r) le_rfl
      (homOfLE (X.basicOpen_le r))) := by
  have (n : ℕ) := AffineChartSectionLocalization.restriction_isLocalized (idealGraded I n) V r
  exact DirectSumLocalization.isLocalizedModule r _

omit [IsLocallyNoetherian X] in
/-- Chart scalars act by the actual structural scalar on the original coefficients. -/
lemma chartTotal_smul (W : X.Opens) (h : W ≤ V.1) (r : Γ(X, V.1))
    (s : chartTotal I V W h) :
    r • s = (X.presheaf.map (homOfLE h).op r) • (show Sections I W from s) := rfl

/-- One power clears denominators in every degree of an actual local coefficient. -/
lemma chartTotal_exists_numerator (r : Γ(X, V.1)) (s : Sections I (X.basicOpen r)) :
    ∃ (n : ℕ) (t : Sections I V.1),
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op r) ^ n • s =
        restrictRingHom I _ (homOfLE (X.basicOpen_le r)) t := by
  let _ := chartTotalRestriction_isLocalized I V r
  obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj
    (chartTotalRestriction I V (X.basicOpen_le r) le_rfl
      (homOfLE (X.basicOpen_le r))) r s
  refine ⟨n, t, ?_⟩
  rw [chartTotal_smul, map_pow, chartTotalRestriction_apply] at ht
  exact ht

/-- One chart-scalar power kills an actual coefficient vanishing on the principal open. -/
lemma chartTotal_exists_annihilator (r : Γ(X, V.1)) (s : Sections I V.1)
    (hs : restrictRingHom I (X.basicOpen r) (homOfLE (X.basicOpen_le r)) s = 0) :
    ∃ n : ℕ, r ^ n • s = 0 := by
  let _ := chartTotalRestriction_isLocalized I V r
  have h : chartTotalRestriction I V (X.basicOpen_le r) le_rfl
      (homOfLE (X.basicOpen_le r)) s =
        chartTotalRestriction I V (X.basicOpen_le r) le_rfl
          (homOfLE (X.basicOpen_le r)) 0 := by
    rw [chartTotalRestriction_apply, map_zero]
    exact hs
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq r h
  refine ⟨n, ?_⟩
  have he := chartTotal_smul I V V.1 le_rfl (r ^ n) s
  have hid : homOfLE (show V.1 ≤ V.1 from le_rfl) = 𝟙 V.1 := Subsingleton.elim _ _
  rw [hid, op_id, X.presheaf.map_id, CommRingCat.id_apply] at he
  exact he.symm.trans (hn.trans (smul_zero _))

end FLT.Mazur.IdealAdicGradedSections
