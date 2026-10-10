/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallySplitSheafPullback

/-!
# Transport and restriction of actual locally split sheaf maps

Source isomorphisms and ordinary open restriction preserve local splitting.
Together with ambient isomorphisms this permits the original inclusion to
be expressed in each varying finite free ambient chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitLineAffineNeighborhood
variable {X Y : Scheme.{u}} {L N : X.Modules} (s : L ⟶ N)

/-- Changing the source by an actual isomorphism preserves local splitting. -/
lemma LocallySplit.precompose {M : X.Modules} (hs : LocallySplit s) (a : M ≅ L) :
    LocallySplit (a.hom ≫ s) := by
  intro x
  obtain ⟨U, hx, hU⟩ := hs x
  let _ := hU
  refine ⟨U, hx, IsSplitMono.mk' ⟨CategoryTheory.retraction
    ((Scheme.Modules.pullback U.ι).map s) ≫ (Scheme.Modules.pullback U.ι).map a.inv, ?_⟩⟩
  rw [Functor.map_comp, Category.assoc, IsSplitMono.id_assoc, ← Functor.map_comp,
    a.hom_inv_id, CategoryTheory.Functor.map_id]

/-- Actual restriction to an open subscheme remains locally split. -/
lemma LocallySplit.restriction (hs : LocallySplit s) (j : Y ⟶ X) [IsOpenImmersion j] :
    LocallySplit ((restrictFunctor j).map s) := by
  let a := restrictFunctorIsoPullback j
  have h : a.hom.app L ≫ (Scheme.Modules.pullback j).map s ≫ a.inv.app N =
      (restrictFunctor j).map s := by
    rw [← a.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [← h]
  exact ((hs.pullback s j).postcompose _ (a.app N).symm).precompose _ (a.app L)

end FLT.Mazur.SplitLineAffineNeighborhood
