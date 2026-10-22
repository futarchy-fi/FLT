/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredFlatRelationDescent

/-!
# One coefficient enlargement for finitely many flatness tests

Every specified finite collection of relations acquires actual trivializing
matrices at one stage. The stage retains the original source and every
witness survives further transitions. No bound on all relations is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
open scoped BigOperators
namespace FLT.Mazur.Approximation
open RingFlatRelation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
variable {I : Type v} [Category.{w} I] [IsFiltered I]
  (F G : I ⥤ CommRingCat.{u}) (c : Cocone F) (d : Cocone G)
  (hc : IsColimit c) (hd : IsColimit d)
  [PreservesColimit F (forget CommRingCat)]
  [PreservesColimit G (forget CommRingCat)]
  (η : F ⟶ G) (φ : c.pt →+* d.pt)
  (hφ : ∀ i, (d.ι.app i).hom.comp (η.app i).hom = φ.comp (c.ι.app i).hom)

include hc hd hφ in
/-- A finite collection of recovered flat relations becomes trivial at one common stage. -/
theorem exists_flat_relation_family_stage (hflat : φ.Flat)
    {T : Type*} [Finite T] (K : T → Type*) [∀ t, Fintype (K t)]
    (i : I) (f : ∀ t, K t → F.obj i) (x : ∀ t, K t → G.obj i)
    (h : ∀ t, let f' : K t → c.pt := fun l ↦ c.ι.app i (f t l)
      let x' : K t → d.pt := fun l ↦ d.ι.app i (x t l)
      ∑ l, φ (f' l) * x' l = 0) :
    ∃ (j : I) (g : i ⟶ j), ∀ t,
      Trivial (η.app j).hom (fun l ↦ F.map g (f t l)) (fun l ↦ G.map g (x t l)) := by
  classical
  choose j g hj using fun t ↦
    exists_flat_relation_stage F G c d hc hd η φ hφ hflat i (f t) (x t) (h t)
  cases nonempty_fintype T
  let A (t : T) : Under i := Under.mk (g t)
  obtain ⟨B, hB⟩ := IsFiltered.sup_objs_exists (Finset.univ.image A)
  refine ⟨B.right, B.hom, fun t ↦ ?_⟩
  let e : A t ⟶ B := (hB (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩)).some
  have he : g t ≫ e.right = B.hom := Under.w e
  have hn : (G.map e.right).hom.comp (η.app (j t)).hom =
      (η.app B.right).hom.comp (F.map e.right).hom := by
    exact congrArg CommRingCat.Hom.hom (η.naturality e.right).symm
  have ht := trivial_map (η.app (j t)).hom (η.app B.right).hom
    (F.map e.right).hom (G.map e.right).hom hn _ _ (hj t)
  change Trivial (η.app B.right).hom
    (fun l ↦ (F.map (g t) ≫ F.map e.right) (f t l))
    (fun l ↦ (G.map (g t) ≫ G.map e.right) (x t l)) at ht
  simpa only [← F.map_comp, ← G.map_comp, he] using ht

end FLT.Mazur.Approximation
