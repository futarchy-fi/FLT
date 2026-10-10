/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredRingFiniteUnits

/-!
# Simultaneous descent in finitely many filtered ring systems

Independent ring colimits indexed by the same filtered category have a
common stage for unit lifts and for detecting finite families of equations.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace FLT.Mazur.Approximation

universe u v w

variable {I : Type v} [Category.{w} I] [IsFiltered I]
  {J : Type*} [Finite J] (F : J → I ⥤ CommRingCat.{u})
  (c : ∀ j, Cocone (F j)) (hc : ∀ j, IsColimit (c j))
  [∀ j, PreservesColimit (F j) (forget CommRingCat)]

include hc in
/-- Finite families of units in different ring systems lift at a common stage. -/
theorem exists_family_unit_lifts (K : J → Type*) [∀ j, Finite (K j)]
    (i : I) (x : ∀ j, K j → (c j).ptˣ) :
    ∃ (a : I) (_ : i ⟶ a) (y : ∀ j, K j → ((F j).obj a)ˣ),
      ∀ j k, Units.map ((c j).ι.app a).hom.toMonoidHom (y j k) = x j k := by
  classical
  choose a f y hy using fun j ↦ exists_unit_lifts_of_finite (F j) (c j) (hc j) i (x j)
  cases nonempty_fintype J
  let A (j : J) : Under i := Under.mk (f j)
  obtain ⟨B, hB⟩ := IsFiltered.sup_objs_exists (Finset.univ.image A)
  let g (j : J) : A j ⟶ B :=
    (hB (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)).some
  refine ⟨B.right, B.hom,
    fun j k ↦ Units.map ((F j).map (g j).right).hom.toMonoidHom (y j k), ?_⟩
  intro j k
  apply Units.ext
  change (c j).ι.app B.right ((F j).map (g j).right (y j k : (F j).obj (a j))) =
    (x j k : (c j).pt)
  exact (congrArg (fun q : (F j).obj (a j) ⟶ (c j).pt ↦ q (y j k))
    ((c j).w (g j).right)).trans (congrArg Units.val (hy j k))

include hc in
/-- Finite equations in different ring systems hold after a common transition. -/
theorem exists_family_map_eq (K : J → Type*) [∀ j, Finite (K j)] (i : I)
    (x y : ∀ j, K j → (F j).obj i)
    (h : ∀ j k, (c j).ι.app i (x j k) = (c j).ι.app i (y j k)) :
    ∃ (a : I) (f : i ⟶ a), ∀ j k, (F j).map f (x j k) = (F j).map f (y j k) := by
  classical
  choose a f ha using fun j ↦ exists_map_eq_of_finite (F j) (c j) (hc j) i
    (x j) (y j) (h j)
  cases nonempty_fintype J
  let A (j : J) : Under i := Under.mk (f j)
  obtain ⟨B, hB⟩ := IsFiltered.sup_objs_exists (Finset.univ.image A)
  refine ⟨B.right, B.hom, fun j k ↦ ?_⟩
  let g : A j ⟶ B := (hB (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)).some
  have hg : f j ≫ g.right = B.hom := Under.w g
  have he := congrArg ((F j).map g.right) (ha j k)
  change ((F j).map (f j) ≫ (F j).map g.right) (x j k) =
    ((F j).map (f j) ≫ (F j).map g.right) (y j k) at he
  rwa [← (F j).map_comp, hg] at he

end FLT.Mazur.Approximation
