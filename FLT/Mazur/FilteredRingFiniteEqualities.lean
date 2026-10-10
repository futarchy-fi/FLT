/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Category.Ring.FinitePresentation

/-!
# Detecting finitely many equalities at one filtered ring stage

Equalities at the colimit between finitely many pairs from a fixed ring
stage already hold after one common transition from that stage.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace FLT.Mazur.Approximation

universe u v w

variable {I : Type v} [Category.{w} I] [IsFiltered I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
  [PreservesColimit F (forget CommRingCat)]

include hc in
/-- Finitely many equalities from one source stage are witnessed by a single transition. -/
theorem exists_map_eq_of_finite {K : Type*} [Finite K] (i : I)
    (a b : K → F.obj i) (h : ∀ k, c.ι.app i (a k) = c.ι.app i (b k)) :
    ∃ (j : I) (f : i ⟶ j), ∀ k, F.map f (a k) = F.map f (b k) := by
  classical
  have hc' := isColimitOfPreserves (forget CommRingCat) hc
  choose j f hj using fun k ↦
    (Types.FilteredColimit.isColimit_eq_iff' hc' (a k) (b k)).mp (h k)
  cases nonempty_fintype K
  let A (k : K) : Under i := Under.mk (f k)
  obtain ⟨B, hB⟩ := IsFiltered.sup_objs_exists (Finset.univ.image A)
  refine ⟨B.right, B.hom, fun k ↦ ?_⟩
  let g : A k ⟶ B := (hB (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)).some
  have hg : f k ≫ g.right = B.hom := Under.w g
  have he := congrArg (F.map g.right) (hj k)
  change (F.map (f k) ≫ F.map g.right) (a k) =
    (F.map (f k) ≫ F.map g.right) (b k) at he
  rwa [← F.map_comp, hg] at he

end FLT.Mazur.Approximation
