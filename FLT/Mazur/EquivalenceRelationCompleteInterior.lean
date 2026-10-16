/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteClosedLocus
public import FLT.Mazur.EquivalenceRelationNormalizedOrbitNeighborhood

/-!
# The maximal open domain of complete normalized frames

The interior of the intrinsic complete locus is stable under the moving action.
Every point of this actual open has a complete stable affine neighborhood whenever
an affine envelope exists. No assertion that all complete points are interior is made.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)

/-- The largest original source open consisting entirely of complete frames. -/
def completeInterior : (source p q I o).Opens :=
  ⟨interior (completePointLocus (p := p) (q := q) I o), isOpen_interior⟩

omit [Etale p] in
/-- The actual interior retains completeness at every one of its points. -/
theorem completeInterior_subset :
    (completeInterior (p := p) (q := q) I o : Set _) ⊆
      completePointLocus (p := p) (q := q) I o := interior_subset

omit [Etale p] in
/-- Every open with complete support lies in the constructed interior. -/
theorem le_completeInterior (U : (source p q I o).Opens)
    (hU : (U : Set _) ⊆ completePointLocus (p := p) (q := q) I o) :
    U ≤ completeInterior (p := p) (q := q) I o :=
  interior_maximal hU U.isOpen

/-- The moving action preserves the actual complete interior. -/
theorem completeInterior_action_invariant (σ : Equiv.Perm I) :
    (action e I o σ).hom ⁻¹ᵁ completeInterior (p := p) (q := q) I o =
      completeInterior (p := p) (q := q) I o := by
  apply TopologicalSpace.Opens.ext
  change (action e I o σ).hom ⁻¹' interior _ = interior _
  rw [(action e I o σ).hom.isOpenMap.preimage_interior_eq_interior_preimage
    (action e I o σ).hom.continuous, completePointLocus_action_invariant e I o σ]

/-- An interior point has its entire finite moving orbit inside the complete interior. -/
theorem frameOrbit_subset_completeInterior (x : source p q I o)
    (hx : x ∈ completeInterior (p := p) (q := q) I o) :
    frameOrbit e I o x ⊆ completeInterior (p := p) (q := q) I o := by
  rintro _ ⟨σ, rfl⟩
  have h := congrArg (fun U : (source p q I o).Opens ↦ x ∈ U)
    (completeInterior_action_invariant e I o σ)
  exact h.to_iff.mpr hx

/-- Actual complete stable affine neighborhoods are constructed at every interior point. -/
theorem exists_completeInterior_affine {Y : Scheme} [IsAffine Y]
    (j : source p q I o ⟶ Y) [IsOpenImmersion j] (x : source p q I o)
    (hx : x ∈ completeInterior (p := p) (q := q) I o) :
    ∃ U : (source p q I o).Opens,
      IsAffineOpen U ∧ frameOrbit e I o x ⊆ U ∧
      (U : Set _) ⊆ completePointLocus (p := p) (q := q) I o ∧
      ∀ σ : Equiv.Perm I, (action e I o σ).hom ⁻¹ᵁ U = U := by
  obtain ⟨U, ha, hxU, hU, hs⟩ := exists_frameOrbit_affine_neighborhood e I o j x
    (completeInterior (p := p) (q := q) I o) (frameOrbit_subset_completeInterior e I o x hx)
  exact ⟨U, ha, hxU, fun y hy ↦ completeInterior_subset I o (hU hy), hs⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
