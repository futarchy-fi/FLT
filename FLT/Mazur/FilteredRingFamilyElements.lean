/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredRingFiniteUnits

/-!
# Lifting finite families of ordinary section coordinates

Ordinary elements in finitely many filtered ring colimits lift at a common
stage above any prescribed starting stage.
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
/-- Finite families of elements in different ring systems lift at a common stage. -/
theorem exists_family_element_lifts (K : J → Type*) [∀ j, Finite (K j)]
    (i : I) (x : ∀ j, K j → (c j).pt) :
    ∃ (a : I) (_ : i ⟶ a) (y : ∀ j, K j → (F j).obj a),
      ∀ j k, (c j).ι.app a (y j k) = x j k := by
  classical
  choose a f y hy using fun j ↦ exists_lifts_of_finite (F j) (c j) (hc j) i (x j)
  cases nonempty_fintype J
  let A (j : J) : Under i := Under.mk (f j)
  obtain ⟨B, hB⟩ := IsFiltered.sup_objs_exists (Finset.univ.image A)
  let g (j : J) : A j ⟶ B :=
    (hB (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)).some
  refine ⟨B.right, B.hom,
    fun j k ↦ (F j).map (g j).right (y j k), ?_⟩
  intro j k
  change (c j).ι.app B.right ((F j).map (g j).right (y j k : (F j).obj (a j))) =
    (x j k : (c j).pt)
  exact (congrArg (fun q : (F j).obj (a j) ⟶ (c j).pt ↦ q (y j k))
    ((c j).w (g j).right)).trans (hy j k)

end FLT.Mazur.Approximation
