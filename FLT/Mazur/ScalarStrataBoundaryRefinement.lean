/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarClosedImageStrata

/-!
# Covering the boundary outside finitely many scalar principal opens

Append the chosen denominators to each stratum's closed equations. This
constructs the entire remaining boundary, with exact residue-closure lifts
and without assuming that an actual scalar image is closed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarConstructibleStrata
variable {R : Type} [CommRing R]

/-- Refine every existing scalar piece by the complement of the chosen principal opens. -/
def boundaryPieces (pieces : Finset (R × Finset R)) (cuts : Finset R) :
    Finset (R × Finset R) := by
  classical
  exact pieces.image fun a ↦ (a.1, a.2 ∪ cuts)

/-- The constructed pieces cover exactly the old set outside all chosen principal opens. -/
theorem boundaryPieces_iff (pieces : Finset (R × Finset R)) (cuts : Finset R)
    (P : PrimeSpectrum R) :
    (∃ a ∈ boundaryPieces pieces cuts,
      a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal) ↔
      (∃ a ∈ pieces, a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal) ∧
        ∀ t ∈ cuts, t ∈ P.asIdeal := by
  classical
  simp only [boundaryPieces, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, ht, he⟩
    exact ⟨⟨a, ha, ht, fun r hr ↦ he r (Finset.mem_union_left _ hr)⟩,
      fun r hr ↦ he r (Finset.mem_union_right _ hr)⟩
  · rintro ⟨⟨a, ha, ht, he⟩, hc⟩
    refine ⟨(a.1, a.2 ∪ cuts), ⟨a, ha, rfl⟩, ht, fun r hr ↦ ?_⟩
    exact (Finset.mem_union.mp hr).elim (he r) (hc r)

variable {S : Type} [CommRing S] (s : R →+* S) (J : Ideal S)

/-- Boundary strata produce closed-source lifts that kill every removed-open denominator. -/
theorem exists_closed_scalar_boundary_strata
    (hfp : ((Ideal.Quotient.mk J).comp s).FinitePresentation) (cuts : Finset R) :
    ∃ pieces : Finset (R × Finset R), ∀ P : PrimeSpectrum R,
      (∃ a ∈ pieces, a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal) ↔
      ∃ w : S →+* AlgebraicClosure P.asIdeal.ResidueField,
        w.comp s = algebraMap R _ ∧ (∀ b ∈ J, w b = 0) ∧
          ∀ t ∈ cuts, w (s t) = 0 := by
  obtain ⟨pieces, h⟩ := ScalarClosedImageCoverage.exists_closed_scalar_image_strata s J hfp
  refine ⟨boundaryPieces pieces cuts, fun P ↦ ?_⟩
  rw [boundaryPieces_iff, h P]
  have hz (w : S →+* AlgebraicClosure P.asIdeal.ResidueField)
      (hw : w.comp s = algebraMap R _) (t : R) :
      w (s t) = 0 ↔ t ∈ P.asIdeal := by
    change (w.comp s) t = 0 ↔ _
    rw [hw, IsScalarTower.algebraMap_apply R P.asIdeal.ResidueField
      (AlgebraicClosure P.asIdeal.ResidueField), map_eq_zero,
      Ideal.algebraMap_residueField_eq_zero]
  constructor
  · rintro ⟨⟨w, hw, hj⟩, hc⟩
    exact ⟨w, hw, hj, fun t ht ↦ (hz w hw t).mpr (hc t ht)⟩
  · rintro ⟨w, hw, hj, hc⟩
    exact ⟨⟨w, hw, hj⟩, fun t ht ↦ (hz w hw t).mp (hc t ht)⟩

end FLT.Mazur.ScalarConstructibleStrata
