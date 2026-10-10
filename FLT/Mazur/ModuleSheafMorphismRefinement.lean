/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafMorphismGluing

/-!
# Checking morphism compatibility on common refinements

Local module maps agree on an entire overlap if they agree on a cover
by common refinements. The criterion tests all subopens of each refinement,
so sheaf separatedness applies without any affine intersection hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u v w

namespace FLT.Mazur.ModuleSheafMorphismGluing

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Local linear maps agree when they agree on all subopens of a common-refinement cover. -/
lemma localApp_eq_of_refinement_cover {U V : X.Opens}
    (a : M.over U ⟶ N.over U) (b : M.over V ⟶ N.over V)
    {κ : Type w} (W : κ → X.Opens)
    (hU : ∀ k, W k ≤ U) (hV : ∀ k, W k ≤ V)
    (hcover : ∀ x ∈ U ⊓ V, ∃ k, x ∈ W k)
    (hab : ∀ k (T : X.Opens) (hT : T ≤ W k),
      localApp a (hT.trans (hU k)) = localApp b (hT.trans (hV k)))
    (T : X.Opens) (hTU : T ≤ U) (hTV : T ≤ V) :
    localApp a hTU = localApp b hTV := by
  ext s
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun k ↦ T ⊓ W k) T (fun _ ↦ homOfLE inf_le_left)
  · intro x hx
    obtain ⟨k, hk⟩ := hcover x ⟨hTU hx, hTV hx⟩
    exact Opens.mem_iSup.mpr ⟨k, hx, hk⟩
  · intro k
    change res N inf_le_left (localApp a hTU s) =
      res N inf_le_left (localApp b hTV s)
    rw [← localApp_res, ← localApp_res]
    exact congrArg (fun c ↦ c (res M inf_le_left s)) (hab k (T ⊓ W k) inf_le_right)

/-- Pairwise common-refinement covers suffice for the full gluing compatibility condition. -/
lemma compatible_of_refinement_covers {ι : Type v} (U : ι → X.Opens)
    (a : ∀ i, M.over (U i) ⟶ N.over (U i))
    (κ : ι → ι → Type w) (W : ∀ i j, κ i j → X.Opens)
    (hleft : ∀ i j k, W i j k ≤ U i) (hright : ∀ i j k, W i j k ≤ U j)
    (hcover : ∀ i j (x : X), x ∈ U i ⊓ U j → ∃ k, x ∈ W i j k)
    (ha : ∀ i j k (T : X.Opens) (hT : T ≤ W i j k),
      localApp (a i) (hT.trans (hleft i j k)) =
        localApp (a j) (hT.trans (hright i j k))) : Compatible U a := by
  intro i j T hi hj
  exact localApp_eq_of_refinement_cover (a i) (a j) (W i j)
    (hleft i j) (hright i j) (hcover i j) (ha i j) T hi hj

end FLT.Mazur.ModuleSheafMorphismGluing
