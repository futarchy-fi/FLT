/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTripleModuleLocalization

/-!
# Extending a projective chart section after twisting

A common power of the distinguished coordinate kills the overlap discrepancies
of chart numerators. The corrected inverse coordinates glue to a global section.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial HomogeneousLocalization

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The regular function `Xᵢ/Xⱼ` on the entire chart `j`. -/
def chartCoordinateSection (j i : ι) : Γ(space R ι, chart R ι j) :=
  (Proj.awayToSection (grading R ι) (X j)).hom (coordinate R ι j i)

/-- The distinguished coordinate is one on its own chart. -/
@[simp]
lemma chartCoordinateSection_self (i : ι) : chartCoordinateSection R ι i i = 1 := by
  simp only [chartCoordinateSection, coordinate_self, map_one]

private lemma chartScalar_restrict (j k : ι) (r : chartRing R ι j) :
    (space R ι).presheaf.map (homOfLE inf_le_left).op
      ((Proj.awayToSection (grading R ι) (X j)).hom r) =
    overlapScalarHom R ι j k (toOverlap R ι j k r) := by
  rw [overlapScalarHom_eq]
  have h := congrArg (fun f ↦ f.hom r)
    (Proj.awayMap_awayToSection (grading R ι) (isHomogeneous_X R k) rfl)
  change _ = (space R ι).presheaf.map (homOfLE (chart_inf R ι j k).le).op
    ((Proj.awayToSection (grading R ι) (X j * X k)).hom (toOverlap R ι j k r))
  change (Proj.awayToSection (grading R ι) (X j * X k)).hom
    (toOverlap R ι j k r) =
    (space R ι).presheaf.map _ ((Proj.awayToSection (grading R ι) (X j)).hom r) at h
  erw [h]
  simp only [← Functor.map_comp_apply]
  rfl

/-- Restricting a chart coordinate gives the specified overlap scalar. -/
lemma chartCoordinateSection_restrict (j k i : ι) :
    (space R ι).presheaf.map (homOfLE inf_le_left).op
      (chartCoordinateSection R ι j i) =
    overlapScalarHom R ι j k (toOverlap R ι j k (coordinate R ι j i)) :=
  chartScalar_restrict R ι j k _

private lemma otherChartScalar_restrict (j k : ι) (r : chartRing R ι k) :
    (space R ι).presheaf.map (homOfLE inf_le_right).op
      ((Proj.awayToSection (grading R ι) (X k)).hom r) =
    overlapScalarHom R ι j k
      (awayMap (grading R ι) (isHomogeneous_X R j) (mul_comm (X j) (X k)) r) := by
  rw [overlapScalarHom_eq]
  have h := congrArg (fun f ↦ f.hom r)
    (Proj.awayMap_awayToSection (grading R ι) (isHomogeneous_X R j)
      (mul_comm (X j) (X k)))
  change _ = (space R ι).presheaf.map (homOfLE (chart_inf R ι j k).le).op
    ((Proj.awayToSection (grading R ι) (X j * X k)).hom _)
  change (Proj.awayToSection (grading R ι) (X j * X k)).hom
    (awayMap (grading R ι) (isHomogeneous_X R j) (mul_comm (X j) (X k)) r) =
    (space R ι).presheaf.map _ ((Proj.awayToSection (grading R ι) (X k)).hom r) at h
  erw [h]
  simp only [← Functor.map_comp_apply]
  rfl

/-- Coordinate multiplication holds on the whole pair overlap, even where `Xᵢ` vanishes. -/
lemma chartCoordinateSection_cocycle (j k i : ι) :
    (space R ι).presheaf.map (homOfLE inf_le_left).op
      (chartCoordinateSection R ι j i) =
    (twistTransition R ι 1 j k : Γ(space R ι, chart R ι j ⊓ chart R ι k)) *
      (space R ι).presheaf.map (homOfLE inf_le_right).op
        (chartCoordinateSection R ι k i) := by
  rw [chartCoordinateSection_restrict, ← overlapScalarHom_coordinate]
  unfold chartCoordinateSection
  erw [otherChartScalar_restrict R ι j k]
  rw [← map_mul]
  apply congrArg (overlapScalarHom R ι j k)
  simp only [toOverlap, coordinate, awayMap_mk]
  apply val_injective
  simp only [val_mul, Away.val_mk, pow_one, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

/-- The discrepancy between chart numerators in the first chart's coordinates. -/
def overlapDiscrepancy (F : (space R ι).Modules) (N : ℕ)
    (t : ∀ j, Γ(F, chart R ι j)) (j k : ι) :
    Γ(F, chart R ι j ⊓ chart R ι k) :=
  F.presheaf.map (homOfLE inf_le_left).op (t j) -
    (twistTransition R ι 1 j k : Γ(space R ι, chart R ι j ⊓ chart R ι k)) ^ N •
      F.presheaf.map (homOfLE inf_le_right).op (t k)

private lemma discrepancy_vanishes (F : (space R ι).Modules) (N : ℕ)
    (t : ∀ j, Γ(F, chart R ι j)) (i : ι) (s : Γ(F, chart R ι i))
    (ht : ∀ j,
      (twistTensor R ι F (N : ℤ)).presheaf.map (homOfLE inf_le_left).op
        ((twistAmbientIso R ι F (N : ℤ) j _ le_rfl).inv (t j)) =
      (twistTensor R ι F (N : ℤ)).presheaf.map (homOfLE inf_le_right).op
        ((twistAmbientIso R ι F (N : ℤ) i _ le_rfl).inv s)) (j k : ι) :
    F.presheaf.map (homOfLE inf_le_left).op
      (overlapDiscrepancy R ι F N t j k) =
      (0 : Γ(F, (chart R ι j ⊓ chart R ι k) ⊓ chart R ι i)) := by
  let G := twistTensor R ι F (N : ℤ)
  let u := fun a ↦ (twistAmbientIso R ι F (N : ℤ) a _ le_rfl).inv (t a)
  let v := (twistAmbientIso R ι F (N : ℤ) i _ le_rfl).inv s
  have h (a : ι) (ha : (chart R ι j ⊓ chart R ι k) ⊓ chart R ι i ≤ chart R ι a) :
      G.presheaf.map (homOfLE ha).op (u a) =
      G.presheaf.map (homOfLE inf_le_right).op v := by
    have ht' := ht a
    change G.presheaf.map (homOfLE inf_le_left).op (u a) =
      G.presheaf.map (homOfLE inf_le_right).op v at ht'
    have e := congrArg (G.presheaf.map (homOfLE (le_inf ha inf_le_right)).op) ht'
    simpa only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using e
  let V := (chart R ι j ⊓ chart R ι k) ⊓ chart R ι i
  have hj : V ≤ chart R ι j := inf_le_left.trans inf_le_left
  have hk : V ≤ chart R ι k := inf_le_left.trans inf_le_right
  let e := twistAmbientIso R ι F (N : ℤ) j V hj
  have he : G.presheaf.map (homOfLE hj).op (u j) =
      G.presheaf.map (homOfLE hk).op (u k) := (h j hj).trans (h k hk).symm
  have ej := (congrArg e.hom
    (twistAmbientIso_inv_restrict R ι F (N : ℤ) j le_rfl hj (t j))).trans
      (ConcreteCategory.congr_hom e.inv_hom_id _)
  have ek := (congrArg e.hom
    (twistAmbientIso_inv_restrict R ι F (N : ℤ) k le_rfl hk (t k))).trans
      (twistAmbientIso_change R ι F (N : ℤ) j k V hj hk _)
  have hc := ej.symm.trans ((congrArg e.hom he).trans ek)
  change F.presheaf.map _ (_ - _) = 0
  rw [map_sub]
  erw [F.val.map_smul]
  rw [map_pow, sub_eq_zero]
  simp only [zpow_natCast, Units.val_pow_eq_pow_val] at hc
  change F.presheaf.map (homOfLE hj).op (t j) =
    ((space R ι).presheaf.map (homOfLE inf_le_left).op
      (twistTransition R ι 1 j k : Γ(space R ι, chart R ι j ⊓ chart R ι k))) ^ N •
      F.presheaf.map (homOfLE hk).op (t k) at hc
  change F.presheaf.map (homOfLE (show V ≤ _ from inf_le_left)).op
      (F.presheaf.map (homOfLE inf_le_left).op (t j)) =
    ((space R ι).presheaf.map (homOfLE inf_le_left).op
      (twistTransition R ι 1 j k : Γ(space R ι, chart R ι j ⊓ chart R ι k))) ^ N •
      F.presheaf.map (homOfLE inf_le_left).op
        (F.presheaf.map (homOfLE inf_le_right).op (t k))
  simpa only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using hc

/-- Raise all chart numerators by a common power of the distinguished coordinate. -/
def correctedChartNumerators (F : (space R ι).Modules) (i : ι) (m : ℕ)
    (t : ∀ j, Γ(F, chart R ι j)) (j : ι) : Γ(F, chart R ι j) :=
  chartCoordinateSection R ι j i ^ m • t j

/-- Raising the twist scales its discrepancy by precisely the same coordinate power. -/
lemma overlapDiscrepancy_corrected (F : (space R ι).Modules) (N m : ℕ) (i : ι)
    (t : ∀ j, Γ(F, chart R ι j)) (j k : ι) :
    overlapDiscrepancy R ι F (N + m) (correctedChartNumerators R ι F i m t) j k =
      overlapScalarHom R ι j k (toOverlap R ι j k (coordinate R ι j i)) ^ m •
        overlapDiscrepancy R ι F N t j k := by
  rw [← chartCoordinateSection_restrict]
  have he :
      (twistTransition R ι 1 j k : Γ(space R ι, chart R ι j ⊓ chart R ι k)) ^ (N + m) *
        ((space R ι).presheaf.map (homOfLE inf_le_right).op
          (chartCoordinateSection R ι k i)) ^ m =
      ((space R ι).presheaf.map (homOfLE inf_le_left).op
        (chartCoordinateSection R ι j i)) ^ m *
        (twistTransition R ι 1 j k : Γ(space R ι, chart R ι j ⊓ chart R ι k)) ^ N := by
    rw [chartCoordinateSection_cocycle, mul_pow, pow_add]
    ring
  simp only [overlapDiscrepancy, correctedChartNumerators]
  erw [F.val.map_smul, F.val.map_smul]
  simp only [map_pow, smul_sub, smul_smul]
  have hresult := congrArg (fun r : Γ(space R ι, chart R ι j ⊓ chart R ι k) ↦
    ((space R ι).presheaf.map
      (homOfLE (show chart R ι j ⊓ chart R ι k ≤ chart R ι j from inf_le_left)).op
      (chartCoordinateSection R ι j i)) ^ m •
      F.presheaf.map
        (homOfLE (show chart R ι j ⊓ chart R ι k ≤ chart R ι j from inf_le_left)).op
        (t j) -
        r • F.presheaf.map
          (homOfLE (show chart R ι j ⊓ chart R ι k ≤ chart R ι k from inf_le_right)).op
          (t k)) he
  exact hresult

/-- One common correction produces compatible coefficients, fixing the original section. -/
theorem sectionExtension_compatibleCoordinates [Finite ι]
    (F : (space R ι).Modules) [F.IsFinitePresentation]
    (i : ι) (s : Γ(F, chart R ι i)) :
    ∃ (d : ℕ) (t : ∀ j, Γ(F, chart R ι j)), t i = s ∧
      ∀ j k, overlapDiscrepancy R ι F d t j k = 0 := by
  obtain ⟨N, t, hi, ht⟩ := sectionExtension_twistCoordinates R ι F i s
  obtain ⟨m, hm⟩ := pairFamily_annihilateKernels_ambient R ι F i
    (overlapDiscrepancy R ι F N t) (discrepancy_vanishes R ι F N t i s ht)
  refine ⟨N + m, correctedChartNumerators R ι F i m t, ?_, fun j k ↦ ?_⟩
  · simp only [correctedChartNumerators, chartCoordinateSection_self, one_pow, one_smul, hi]
  · rw [overlapDiscrepancy_corrected]
    exact hm j k

/-- Every section on a standard chart extends to an actual global section after twisting. -/
theorem sectionExtension_global [Finite ι] (F : (space R ι).Modules)
    [F.IsFinitePresentation] (i : ι) (s : Γ(F, chart R ι i)) :
    ∃ (d : ℕ) (σ : Γ(twistTensor R ι F (d : ℤ), ⊤)),
      (twistAmbientIso R ι F (d : ℤ) i (chart R ι i) le_rfl).hom
        ((twistTensor R ι F (d : ℤ)).presheaf.map (homOfLE le_top).op σ) = s := by
  obtain ⟨d, t, hi, ht⟩ := sectionExtension_compatibleCoordinates R ι F i s
  let G := twistTensor R ι F (d : ℤ)
  let u := fun j ↦ (twistAmbientIso R ι F (d : ℤ) j _ le_rfl).inv (t j)
  have hu (j k : ι) : G.presheaf.map (homOfLE inf_le_left).op (u j) =
      G.presheaf.map (homOfLE inf_le_right).op (u k) := by
    dsimp only [u, G]
    rw [twistAmbientIso_inv_restrict, twistAmbientIso_inv_restrict]
    apply twistAmbientIso_inv_eq
    rw [twistTransition_restrict_self_pow]
    exact sub_eq_zero.mp (ht j k)
  obtain ⟨σ, hσ, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨G.presheaf, G.isSheaf⟩ : TopCat.Sheaf Ab (space R ι))
    (chart R ι) ⊤ (fun _ ↦ homOfLE le_top) (by rw [iSup_chart]) u hu
  refine ⟨d, σ, ?_⟩
  change (twistAmbientIso R ι F (d : ℤ) i _ le_rfl).hom
    (G.presheaf.map (homOfLE le_top).op σ) = s
  rw [hσ i]
  exact (ConcreteCategory.congr_hom
    (twistAmbientIso R ι F (d : ℤ) i _ le_rfl).inv_hom_id (t i)).trans hi

end FLT.Mazur.ProjectiveSpace
