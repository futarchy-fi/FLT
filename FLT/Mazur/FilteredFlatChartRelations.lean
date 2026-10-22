/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredFlatRelationDescent

/-!
# Finite flatness tests on several algebra charts at once

Different affine charts have different algebra rings but share the base
coefficient system. One refinement trivializes a specified relation on
each of finitely many charts, including different relation lengths.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
open scoped BigOperators
namespace FLT.Mazur.Approximation
open RingFlatRelation
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {I : Type v} [Category.{w} I] [IsFiltered I]
  {T : Type*} [Finite T] (F : I ⥤ CommRingCat.{u}) (G : T → I ⥤ CommRingCat.{u})
  (c : Cocone F) (d : ∀ t, Cocone (G t))
  (hc : IsColimit c) (hd : ∀ t, IsColimit (d t))
  [PreservesColimit F (forget CommRingCat)]
  [∀ t, PreservesColimit (G t) (forget CommRingCat)]
  (η : ∀ t, F ⟶ G t) (φ : ∀ t, c.pt →+* (d t).pt)
  (hφ : ∀ t i, ((d t).ι.app i).hom.comp ((η t).app i).hom =
    (φ t).comp (c.ι.app i).hom)

include hc hd hφ in
/-- Independent flat chart relations have witnesses over one common base coefficient stage. -/
theorem exists_flat_chart_relations_stage (hflat : ∀ t, (φ t).Flat)
    (K : T → Type*) [∀ t, Fintype (K t)] (i : I)
    (f : ∀ t, K t → F.obj i) (x : ∀ t, K t → (G t).obj i)
    (h : ∀ t, let f' : K t → c.pt := fun l ↦ c.ι.app i (f t l)
      let x' : K t → (d t).pt := fun l ↦ (d t).ι.app i (x t l)
      ∑ l, φ t (f' l) * x' l = 0) :
    ∃ (j : I) (g : i ⟶ j), ∀ t,
      Trivial ((η t).app j).hom (fun l ↦ F.map g (f t l))
        (fun l ↦ (G t).map g (x t l)) := by
  classical
  choose j g hj using fun t ↦ exists_flat_relation_stage F (G t) c (d t) hc (hd t)
    (η t) (φ t) (hφ t) (hflat t) i (f t) (x t) (h t)
  cases nonempty_fintype T
  let A (t : T) : Under i := Under.mk (g t)
  obtain ⟨B, hB⟩ := IsFiltered.sup_objs_exists (Finset.univ.image A)
  refine ⟨B.right, B.hom, fun t ↦ ?_⟩
  let e : A t ⟶ B := (hB (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩)).some
  have he : g t ≫ e.right = B.hom := Under.w e
  have hn : ((G t).map e.right).hom.comp ((η t).app (j t)).hom =
      ((η t).app B.right).hom.comp (F.map e.right).hom :=
    congrArg CommRingCat.Hom.hom ((η t).naturality e.right).symm
  have ht := trivial_map ((η t).app (j t)).hom ((η t).app B.right).hom
    (F.map e.right).hom ((G t).map e.right).hom hn _ _ (hj t)
  change Trivial ((η t).app B.right).hom
    (fun l ↦ (F.map (g t) ≫ F.map e.right) (f t l))
    (fun l ↦ ((G t).map (g t) ≫ (G t).map e.right) (x t l)) at ht
  simpa only [← F.map_comp, ← (G t).map_comp, he] using ht

end FLT.Mazur.Approximation
