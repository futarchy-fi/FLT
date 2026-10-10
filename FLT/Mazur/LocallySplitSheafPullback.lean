/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitLineAffineNeighborhood
public import FLT.Mazur.LocallySplitInclusionPullback

/-!
# Local splitting survives geometric pullback

Local splitting can be checked by either ordinary restriction or geometric
open pullback. It survives arbitrary base change and ambient isomorphisms,
so the canonical free-sheaf pullback inclusion is locally split as well.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitLineAffineNeighborhood
variable {X Y : Scheme.{u}} {L N : X.Modules} (s : L ⟶ N)

/-- Local geometric splittings give the original restriction splittings. -/
lemma LocallySplit.restrict (hs : LocallySplit s) :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsSplitMono ((restrictFunctor U.ι).map s) := by
  intro x
  obtain ⟨U, hx, hU⟩ := hs x
  let _ := hU
  let a := restrictFunctorIsoPullback U.ι
  refine ⟨U, hx, IsSplitMono.mk' ⟨a.hom.app N ≫
    CategoryTheory.retraction ((Scheme.Modules.pullback U.ι).map s) ≫ a.inv.app L, ?_⟩⟩
  rw [← Category.assoc, a.hom.naturality]
  simp only [Category.assoc, IsSplitMono.id_assoc, Iso.hom_inv_id_app]

/-- Local splitting is preserved by arbitrary geometric base change. -/
lemma LocallySplit.pullback (hs : LocallySplit s) (f : Y ⟶ X) :
    LocallySplit ((Scheme.Modules.pullback f).map s) := by
  apply locallySplit_of_restrict
  intro y
  obtain ⟨U, hy, hU⟩ := hs.restrict s (f y)
  let _ := hU
  exact ⟨f ⁻¹ᵁ U, hy, inferInstance⟩

/-- Replacing the ambient sheaf by an isomorphic one preserves local splitting. -/
lemma LocallySplit.postcompose {M : X.Modules} (hs : LocallySplit s) (a : N ≅ M) :
    LocallySplit (s ≫ a.hom) := by
  intro x
  obtain ⟨U, hx, hU⟩ := hs x
  let _ := hU
  refine ⟨U, hx, IsSplitMono.mk' ⟨(Scheme.Modules.pullback U.ι).map a.inv ≫
    CategoryTheory.retraction ((Scheme.Modules.pullback U.ι).map s), ?_⟩⟩
  rw [Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp_assoc, a.hom_inv_id,
    Category.comp_id, IsSplitMono.id]

/-- The actual canonical free-sheaf inclusion remains locally split after base change. -/
lemma LocallySplit.inclusion {ι : Type u} {L : X.Modules}
    {s : L ⟶ SheafOfModules.free ι} (hs : LocallySplit s) (f : Y ⟶ X) :
    LocallySplit (SplitSheafLinePullback.inclusion f s) :=
  (hs.pullback s f).postcompose _ (ModuleGlobalEvaluationPullback.freeIso f ι)

end FLT.Mazur.SplitLineAffineNeighborhood
