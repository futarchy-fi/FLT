/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedStages
public import FLT.LocalClassFieldTheory.UnramifiedEmbeddings

/-!
# Containment and uniqueness of unramified stages

In a common separable overfield, residue-degree divisibility gives a field
embedding. Normality identifies its image with the original intermediate
field, proving literal containment and uniqueness of each degree.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing

variable {R K C : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)]
  {E F : IntermediateField K C}

/-- Divisibility of degrees gives containment of actual unramified stages. -/
theorem IsUnramifiedStage.le_of_finrank_dvd
    (hE : IsUnramifiedStage R K E) (hF : IsUnramifiedStage R K F)
    (h : Module.finrank K E ∣ Module.finrank K F) : E ≤ F := by
  let : Normal K E := hE.normal
  obtain ⟨_, S, _, _, _, _, _, _, _, _, _, huS, hhS⟩ := hE
  obtain ⟨_, T, _, _, _, _, _, _, _, _, _, huT, hhT⟩ := hF
  let := huS
  let := hhS
  let := huT
  let := hhT
  have hdS := finrank_eq_of_formallyUnramified R S K E
  have hdT := finrank_eq_of_formallyUnramified R T K F
  obtain ⟨f⟩ := nonempty_algHom_of_residue_degree_dvd (R := R) (S := S) (T := T)
    (K := K) (L := E) (M := F) (hdS ▸ hdT ▸ h)
  intro x hx
  rw [← AlgHom.fieldRange_of_normal (F.val.comp f)] at hx
  obtain ⟨y, rfl⟩ := hx
  exact (f y).property

/-- Containment of unramified stages is exactly divisibility of their degrees. -/
theorem IsUnramifiedStage.le_iff_finrank_dvd
    (hE : IsUnramifiedStage R K E) (hF : IsUnramifiedStage R K F) :
    E ≤ F ↔ Module.finrank K E ∣ Module.finrank K F :=
  ⟨IntermediateField.finrank_dvd_of_le_right, hE.le_of_finrank_dvd hF⟩

/-- Two unramified subextensions of the same degree in a common overfield are equal. -/
theorem IsUnramifiedStage.eq_of_finrank_eq
    (hE : IsUnramifiedStage R K E) (hF : IsUnramifiedStage R K F)
    (h : Module.finrank K E = Module.finrank K F) : E = F :=
  le_antisymm (hE.le_of_finrank_dvd hF (h ▸ dvd_refl _))
    (hF.le_of_finrank_dvd hE (h ▸ dvd_refl _))

/-- In the chosen separable closure there is exactly one unramified stage of each degree. -/
theorem existsUnique_unramified_stage [IsSepClosed C]
    [IsAdicComplete (maximalIdeal R) R] (n : ℕ) [NeZero n] :
    ∃! E : IntermediateField K C, IsUnramifiedStage R K E ∧ Module.finrank K E = n := by
  obtain ⟨E, hE, hd⟩ := exists_unramified_stage (R := R) (K := K) C n
  exact ⟨E, ⟨hE, hd⟩, fun F hF => hF.1.eq_of_finrank_eq hE (hF.2.trans hd.symm)⟩

end LocalClassFieldTheory
