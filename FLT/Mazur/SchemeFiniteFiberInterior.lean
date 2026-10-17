/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOpenEnvelopeInteriorTests
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Whole good fibers over the finite target locus

The union of target opens where a morphism is finite is constructed without
assuming global finiteness. A whole good fiber over this locus survives the
closure of the bad image. This is a local closedness argument, not a claim
that good fibers of an arbitrary morphism have open neighborhoods.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y X : Scheme} (f : Y ⟶ X) (O : Y.Opens)

/-- Target points with an actual neighborhood on which the whole morphism is finite. -/
def finiteTargetOpen : X.Opens :=
  ⨆ B : {B : X.Opens // IsFinite (f ∣_ B)}, B.val

/-- The finite target locus retains the neighborhood and its full restricted morphism. -/
theorem mem_finiteTargetOpen (x : X) :
    x ∈ finiteTargetOpen f ↔ ∃ B : X.Opens, IsFinite (f ∣_ B) ∧ x ∈ B := by
  simp only [finiteTargetOpen, Opens.mem_iSup, Subtype.exists, exists_prop]

/-- A globally finite morphism has the entire target as its finite locus. -/
theorem finiteTargetOpen_eq_top [IsFinite f] : finiteTargetOpen f = ⊤ := by
  apply top_unique
  exact le_iSup_of_le ⟨⊤, inferInstance⟩ le_rfl

/-- Pushing a restricted full-fiber neighborhood back into the original target is valid. -/
theorem restrict_fullFiberInterior_image_le (B : X.Opens) :
    B.ι ''ᵁ fullFiberInterior (f ∣_ B) ((f ⁻¹ᵁ B).ι ⁻¹ᵁ O) ≤
      fullFiberInterior f O := by
  apply (le_fullFiberInterior_iff f O _).mpr
  intro y hy
  obtain ⟨x, hx, he⟩ := hy
  have hyB : f y ∈ B := he ▸ x.property
  apply preimage_fullFiberInterior_le (f ∣_ B) ((f ⁻¹ᵁ B).ι ⁻¹ᵁ O)
    (x := ⟨y, hyB⟩)
  change (f ∣_ B) ⟨y, hyB⟩ ∈ fullFiberInterior _ _
  have he' : (f ∣_ B) ⟨y, hyB⟩ = x := by
    apply Subtype.ext
    have h := congrArg (fun g ↦ g ⟨y, hyB⟩) (morphismRestrict_ι f B)
    exact h.trans he.symm
  rwa [he']

/-- A good fiber over the finite target locus avoids the closure of every bad source point. -/
theorem mem_fullFiberInterior_of_finiteTarget (x : X)
    (hx : x ∈ finiteTargetOpen f) (hO : ∀ y : Y, f y = x → y ∈ O) :
    x ∈ fullFiberInterior f O := by
  obtain ⟨B, hB, hxB⟩ := (mem_finiteTargetOpen f x).mp hx
  let _ := hB
  apply restrict_fullFiberInterior_image_le f O B
  refine ⟨⟨x, hxB⟩, ?_, rfl⟩
  apply mem_fullFiberInterior_of_isClosed_image
    (f ∣_ B) ((f ⁻¹ᵁ B).ι ⁻¹ᵁ O)
    ((f ∣_ B).isClosedMap _ ((f ⁻¹ᵁ B).ι ⁻¹ᵁ O).isOpen.isClosed_compl)
  intro y hy
  have h := congrArg (fun g ↦ g y) (morphismRestrict_ι f B)
  exact hO y.val (h.symm.trans (congrArg Subtype.val hy))

/-- On the finite locus, the full-fiber set has no missing interior points. -/
theorem finiteTarget_inter_fullFiberLocus :
    (finiteTargetOpen f : Set X) ∩ fullFiberLocus f O =
      (finiteTargetOpen f : Set X) ∩ fullFiberInterior f O := by
  ext x
  constructor
  · rintro ⟨hx, hO⟩
    exact ⟨hx, mem_fullFiberInterior_of_finiteTarget f O x hx
      (fun y hy ↦ (mem_fullFiberLocus f O x).mp hO y hy)⟩
  · exact fun hx ↦ ⟨hx.1, fullFiberInterior_subset f O hx.2⟩

end FLT.Mazur.SchemeOpenEnvelope
