/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallySplitSheafTransport

/-!
# Descent of local splitting on open covers

A splitting on a subopen of a chart gives a splitting on its image in the
original scheme. Thus the actual sheaf map is locally split exactly when
its geometric pullbacks to a covering family of opens are locally split.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.SplitLineAffineNeighborhood

/-- Naturally isomorphic functors preserve the same split monomorphisms. -/
lemma isSplitMono_map_of_iso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {M N : C} (s : M ⟶ N)
    [IsSplitMono (F.map s)] : IsSplitMono (G.map s) := by
  refine IsSplitMono.mk' ⟨e.inv.app N ≫ retraction (F.map s) ≫ e.hom.app M, ?_⟩
  rw [← Category.assoc, ← Category.assoc, e.inv.naturality]
  simp only [Category.assoc, IsSplitMono.id_assoc, Iso.inv_hom_id_app]

variable {X : Scheme.{u}} {M N : X.Modules} (s : M ⟶ N)

/-- A splitting on an arbitrary open immersion gives one on its actual image. -/
lemma split_on_image {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    [IsSplitMono ((restrictFunctor j).map s)] :
    IsSplitMono ((restrictFunctor j.opensRange.ι).map s) := by
  let e := (restrictFunctorComp j.isoOpensRange.inv j).symm ≪≫
    restrictFunctorCongr j.isoOpensRange_inv_comp
  have : IsSplitMono ((restrictFunctor j ⋙
      restrictFunctor j.isoOpensRange.inv).map s) := by
    change IsSplitMono ((restrictFunctor j.isoOpensRange.inv).map
      ((restrictFunctor j).map s))
    infer_instance
  exact isSplitMono_map_of_iso e s

/-- Local splitting descends through an open cover, retaining the original map. -/
theorem locallySplit_of_openCover {ι : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hs : ∀ i, LocallySplit ((pullback (U i).ι).map s)) : LocallySplit s := by
  apply locallySplit_of_restrict
  intro x
  obtain ⟨i, hx⟩ := Opens.mem_iSup.mp (show x ∈ iSup U by rw [hU]; trivial)
  let a := restrictFunctorIsoPullback (U i).ι
  have hr : LocallySplit ((restrictFunctor (U i).ι).map s) := by
    have he : a.hom.app M ≫ (pullback (U i).ι).map s ≫ a.inv.app N =
        (restrictFunctor (U i).ι).map s := by
      rw [← a.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [← he]
    exact ((hs i).postcompose _ (a.app N).symm).precompose _ (a.app M)
  obtain ⟨V, hv, hV⟩ := hr.restrict _ ⟨x, hx⟩
  let _ := hV
  have : IsSplitMono ((restrictFunctor (U i).ι ⋙ restrictFunctor V.ι).map s) := hV
  have : IsSplitMono ((restrictFunctor (V.ι ≫ (U i).ι)).map s) :=
    isSplitMono_map_of_iso (restrictFunctorComp V.ι (U i).ι).symm s
  refine ⟨(V.ι ≫ (U i).ι).opensRange, ?_, split_on_image s _⟩
  exact ⟨⟨⟨x, hx⟩, hv⟩, rfl⟩

/-- Local splitting of a global map is equivalent to local splitting on every chart. -/
theorem locallySplit_openCover_iff {ι : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    LocallySplit s ↔ ∀ i, LocallySplit ((pullback (U i).ι).map s) :=
  ⟨fun hs i ↦ hs.pullback s (U i).ι, locallySplit_of_openCover s U hU⟩

end FLT.Mazur.SplitLineAffineNeighborhood
