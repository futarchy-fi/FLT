/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafStableSupportCriterion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# A constructed dense open where full ideal powers stabilize

Remove precisely the frontier of the closed support. The pulled original
ideal has open closed support there, so its full powers stabilize. This
construction works without global openness of the original support.
-/

@[expose] public noncomputable section
open AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.IdealSheafClopenStabilization
variable {X : Scheme.{0}} (I : X.IdealSheafData)

/-- The actual open complement of the support frontier in the unchanged ambient scheme. -/
def stableOpen : X.Opens :=
  ⟨(frontier (I.support : Set X))ᶜ, isClosed_frontier.isOpen_compl⟩

/-- The removed locus is closed with empty interior, even when the support is not open. -/
theorem stableOpen_complement_interior :
    interior ((stableOpen I : Set X)ᶜ) = ∅ := by
  change interior (((frontier (I.support : Set X))ᶜ)ᶜ) = ∅
  rw [compl_compl]
  exact interior_frontier I.support.isClosed

/-- The constructed open is dense in the original ambient scheme. -/
theorem stableOpen_dense : Dense (stableOpen I : Set X) := by
  simpa only [compl_compl] using
    interior_eq_empty_iff_dense_compl.mp (stableOpen_complement_interior I)

/-- On this open the exact pulled ideal, with nilpotents retained, has open support. -/
theorem stableOpen_support_isOpen :
    IsOpen ((I.comap (stableOpen I).ι).support : Set (stableOpen I).toScheme) := by
  rw [Scheme.IdealSheafData.support_comap]
  have he : (stableOpen I).ι ⁻¹' (I.support : Set X) =
      (stableOpen I).ι ⁻¹' interior (I.support : Set X) := by
    ext x
    constructor
    · intro hx
      rw [← self_sdiff_frontier]
      exact ⟨hx, x.property⟩
    · exact fun hx ↦ interior_subset (s := (I.support : Set X)) hx
  change IsOpen ((stableOpen I).ι ⁻¹' (I.support : Set X))
  rw [he]
  exact isOpen_interior.preimage (stableOpen I).ι.continuous

/-- One threshold stabilizes all powers on the constructed dense open. -/
theorem exists_stable_on_stableOpen [IsNoetherian X] :
    ∃ K : ℕ, ∀ l, K ≤ l →
      (I.comap (stableOpen I).ι) ^ (l + 1) =
        (I.comap (stableOpen I).ι) ^ (K + 1) := by
  let _ : NoetherianSpace (stableOpen I).toScheme :=
    NoetherianSpace.set (stableOpen I : Set X)
  let _ : IsNoetherian (stableOpen I).toScheme := ⟨⟩
  exact exists_stable _ (stableOpen_support_isOpen I)

end FLT.Mazur.IdealSheafClopenStabilization
