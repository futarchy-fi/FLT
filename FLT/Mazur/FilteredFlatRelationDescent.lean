/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredRingPairWitnesses
public import FLT.Mazur.RingFlatRelation

/-!
# Descending individual flatness witnesses to an actual filtered stage

Both the base coefficients and the algebra generators are lifted, and their
two families of equations are detected after one further transition. The
result concerns a specified relation on a fixed model. It does not exchange
the quantifiers to assert one flat stage for all relations.
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
/-- A specified relation trivial at the colimit is trivial after a finite-stage transition. -/
theorem exists_trivial_relation_stage {K : Type*} [Fintype K]
    (i : I) (f : K → F.obj i) (x : K → G.obj i)
    (h : Trivial φ (fun t ↦ c.ι.app i (f t)) (fun t ↦ d.ι.app i (x t))) :
    ∃ (j : I) (g : i ⟶ j),
      Trivial (η.app j).hom (fun t ↦ F.map g (f t)) (fun t ↦ G.map g (x t)) := by
  obtain ⟨n, a, y, hx, ha⟩ := h
  obtain ⟨j, g, b, z, hb, hz⟩ := exists_pair_element_lifts F G c d hc hd i
    (fun t : K × Fin n ↦ a t.1 t.2) y
  have hf (t : K) : c.ι.app j (F.map g (f t)) = c.ι.app i (f t) :=
    congrArg (fun q : F.obj i ⟶ c.pt ↦ q (f t)) (c.w g)
  have hxx (t : K) : d.ι.app j (G.map g (x t)) = d.ι.app i (x t) :=
    congrArg (fun q : G.obj i ⟶ d.pt ↦ q (x t)) (d.w g)
  have hs (r : F.obj j) : d.ι.app j (η.app j r) = φ (c.ι.app j r) :=
    RingHom.congr_fun (hφ j) r
  have hbase (l : Fin n) :
      c.ι.app j (∑ t, F.map g (f t) * b (t, l)) = c.ι.app j 0 := by
    simpa only [map_sum, map_mul, map_zero, hf, hb] using ha l
  have halg (t : K) : d.ι.app j (G.map g (x t)) =
      d.ι.app j (∑ l, η.app j (b (t, l)) * z l) := by
    simpa only [map_sum, map_mul, hxx, hs, hb, hz] using hx t
  obtain ⟨k, e, he, he'⟩ := exists_pair_map_eq F G c d hc hd j
    (fun l ↦ ∑ t, F.map g (f t) * b (t, l)) (fun _ ↦ 0)
    (fun t ↦ G.map g (x t)) (fun t ↦ ∑ l, η.app j (b (t, l)) * z l) hbase halg
  have hn (r : F.obj j) : G.map e (η.app j r) = η.app k (F.map e r) :=
    (congrArg (fun q : F.obj j ⟶ G.obj k ↦ q r) (η.naturality e)).symm
  refine ⟨k, g ≫ e, n, fun t l ↦ F.map e (b (t, l)),
    fun l ↦ G.map e (z l), fun t ↦ ?_, fun l ↦ ?_⟩
  · simpa only [G.map_comp, CommRingCat.comp_apply, map_sum, map_mul, hn] using he' t
  · simpa only [F.map_comp, CommRingCat.comp_apply, map_sum, map_mul, map_zero] using he l

include hc hd hφ in
/-- Flatness of the recovered ring map trivializes each model relation at some later stage. -/
theorem exists_flat_relation_stage (hflat : φ.Flat) {K : Type*} [Fintype K]
    (i : I) (f : K → F.obj i) (x : K → G.obj i)
    (h : let f' : K → c.pt := fun t ↦ c.ι.app i (f t)
      let x' : K → d.pt := fun t ↦ d.ι.app i (x t)
      ∑ t, φ (f' t) * x' t = 0) :
    ∃ (j : I) (g : i ⟶ j),
      Trivial (η.app j).hom (fun t ↦ F.map g (f t)) (fun t ↦ G.map g (x t)) :=
  exists_trivial_relation_stage F G c d hc hd η φ hφ i f x
    (trivial_of_flat φ hflat _ _ h)

end FLT.Mazur.Approximation
