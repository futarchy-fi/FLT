/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitSheafLinePullbackComposition

/-!
# Affine framed split neighborhoods

Pointwise local rank one and local splitting give simultaneous affine
neighborhoods. The frame and retraction are constructed on a smaller affine
open inside the intersection of their original neighborhoods.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitLineAffineNeighborhood
open FCurve SplitSheafLinePullback
variable {X : Scheme.{u}} {L N : X.Modules}

/-- Local splitting of the actual sheaf map, expressed by geometric open pullback. -/
def LocallySplit (s : L ⟶ N) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsSplitMono ((pullback U.ι).map s)

/-- Ordinary restriction splittings imply geometric local splittings. -/
lemma locallySplit_of_restrict (s : L ⟶ N)
    (hs : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsSplitMono ((restrictFunctor U.ι).map s)) : LocallySplit s := by
  intro x
  obtain ⟨U, hx, hU⟩ := hs x
  let _ := hU
  let a := restrictFunctorIsoPullback U.ι
  refine ⟨U, hx, IsSplitMono.mk' ⟨a.inv.app N ≫
    CategoryTheory.retraction ((restrictFunctor U.ι).map s) ≫ a.hom.app L, ?_⟩⟩
  rw [← Category.assoc, a.inv.naturality]
  simp only [Category.assoc, IsSplitMono.id_assoc, Iso.inv_hom_id_app]

variable {ι : Type u} (s : L ⟶ SheafOfModules.free ι)

/-- A split actual pullback yields a retraction in canonical free-sheaf coordinates. -/
def canonicalRetraction (U : X.Opens) [IsSplitMono ((pullback U.ι).map s)] :
    SheafOfModules.free ι ⟶ (pullback U.ι).obj L :=
  (ModuleGlobalEvaluationPullback.freeIso U.ι ι).inv ≫
    CategoryTheory.retraction ((pullback U.ι).map s)

/-- The canonical retraction splits the geometric inclusion. -/
lemma canonicalRetraction_id (U : X.Opens) [IsSplitMono ((pullback U.ι).map s)] :
    inclusion U.ι s ≫ canonicalRetraction s U = 𝟙 _ := by
  simp only [inclusion, canonicalRetraction, Category.assoc, Iso.hom_inv_id_assoc,
    IsSplitMono.id]

/-- Local rank one and local splitting construct simultaneous affine framed split charts. -/
lemma exists_affine (hL : LocallyFreeRankOne L) (hs : LocallySplit s) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      Nonempty ((pullback U.ι).obj L ≅ structureModule U.toScheme) ∧
      ∃ r : SheafOfModules.free ι ⟶ (pullback U.ι).obj L, inclusion U.ι s ≫ r = 𝟙 _ := by
  obtain ⟨V, hxV, ⟨e⟩⟩ := hL x
  obtain ⟨W, hxW, hW⟩ := hs x
  let _ := hW
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ V ⊓ W from ⟨hxV, hxW⟩) (V ⊓ W).isOpen
  have hUV : U ≤ V := fun _ h ↦ (hUVW h).1
  have hUW : U ≤ W := fun _ h ↦ (hUVW h).2
  let eV := ((restrictFunctorIsoPullback V.ι).app L).symm ≪≫ e
  refine ⟨U, hxU, hU,
    ⟨frameOver (X.homOfLE hUV) V.ι (X.homOfLE_ι hUV) eV⟩,
    retractionOver (X.homOfLE hUW) W.ι (X.homOfLE_ι hUW)
      (canonicalRetraction s W), ?_⟩
  exact inclusion_retractionOver (X.homOfLE hUW) W.ι s (X.homOfLE_ι hUW)
    (canonicalRetraction s W) (canonicalRetraction_id s W)

end FLT.Mazur.SplitLineAffineNeighborhood
