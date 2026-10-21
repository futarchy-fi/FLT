/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafStableOpen

/-!
# The largest original open with stationary full ideal powers

An open has open pulled support exactly when it avoids the original
support frontier. On a Noetherian ambient scheme this characterizes all
open restrictions where full powers stabilize, including their nilpotents.
-/

@[expose] public noncomputable section
open AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.IdealSheafClopenStabilization
variable {X : Scheme.{0}} (I : X.IdealSheafData) (U : X.Opens)

/-- Avoiding the original frontier is equivalent to openness of the full pulled support. -/
theorem support_comap_isOpen_iff_le_stableOpen :
    IsOpen ((I.comap U.ι).support : Set U.toScheme) ↔ U ≤ stableOpen I := by
  rw [Scheme.IdealSheafData.support_comap]
  change IsOpen (U.ι ⁻¹' (I.support : Set X)) ↔ _
  constructor
  · intro ho x hx
    have hi : IsOpen ((I.support : Set X) ∩ U) := by
      have h := U.ι.isOpenEmbedding.isOpenMap _ ho
      rwa [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι] at h
    intro hf
    have hz : x ∈ I.support := I.support.isClosed.frontier_subset hf
    have hint : x ∈ interior (I.support : Set X) :=
      interior_maximal Set.inter_subset_left hi ⟨hz, hx⟩
    exact ((mem_frontier_iff_notMem_interior hz).mp hf) hint
  · intro hU
    have he : U.ι ⁻¹' (I.support : Set X) =
        U.ι ⁻¹' interior (I.support : Set X) := by
      ext x
      constructor
      · intro hx
        rw [← self_sdiff_frontier]
        exact ⟨hx, hU x.property⟩
      · exact fun hx ↦ interior_subset (s := (I.support : Set X)) hx
    rw [he]
    exact isOpen_interior.preimage U.ι.continuous

/-- Full power stabilization on an open is equivalent to containment in the constructed region. -/
theorem exists_stable_on_open_iff [IsNoetherian X] :
    (∃ K : ℕ, ∀ l, K ≤ l → (I.comap U.ι) ^ (l + 1) =
      (I.comap U.ι) ^ (K + 1)) ↔ U ≤ stableOpen I := by
  let _ : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set X)
  let _ : IsNoetherian U.toScheme := ⟨⟩
  rw [exists_stable_iff_support_isOpen, support_comap_isOpen_iff_le_stableOpen]

/-- At a frontier point every original open neighborhood has nonstationary full powers. -/
theorem pow_succ_ne_on_neighborhood_of_frontier [IsLocallyNoetherian X]
    (x : X) (hx : x ∈ frontier (I.support : Set X)) (hU : x ∈ U) (K : ℕ) :
    (I.comap U.ι) ^ (K + 1 + 1) ≠ (I.comap U.ι) ^ (K + 1) := by
  intro hK
  have ho := support_isOpen_of_pow_succ_eq (I.comap U.ι) K hK
  exact ((support_comap_isOpen_iff_le_stableOpen I U).mp ho hU) hx

end FLT.Mazur.IdealSheafClopenStabilization
