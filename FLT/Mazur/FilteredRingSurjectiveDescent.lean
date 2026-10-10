/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredRingFiniteEqualities

/-!
# Surjectivity descends through quotient transition systems

For a filtered ring diagram with surjective transitions, a finite-type map
into one stage becomes surjective at a later stage if its composite with
the colimit map is surjective. Only finitely many generator equations are needed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace FLT.Mazur.Approximation

universe u v w

variable {I : Type v} [Category.{w} I] [IsFiltered I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
  [PreservesColimit F (forget CommRingCat)]

include hc in
/-- Surjectivity to the colimit of a quotient system occurs after one transition. -/
theorem exists_surjective_map_of_isColimit (i : I) {R : CommRingCat.{u}}
    (a : R ⟶ F.obj i) (ha : a.hom.FiniteType)
    (htrans : ∀ {j k} (g : j ⟶ k), Function.Surjective (F.map g))
    (h : Function.Surjective (a ≫ c.ι.app i)) :
    ∃ (j : I) (f : i ⟶ j), Function.Surjective (a ≫ F.map f) := by
  classical
  let _ : Algebra R (F.obj i) := a.hom.toAlgebra
  let _ : Algebra.FiniteType R (F.obj i) := ha
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R (F.obj i)).out
  choose r hr using fun x : s ↦ h (c.ι.app i x.val)
  obtain ⟨j, f, hf⟩ := exists_map_eq_of_finite F c hc i
    (fun x : s ↦ a (r x)) (fun x : s ↦ x.val) hr
  let _ : Algebra R (F.obj j) := (a ≫ F.map f).hom.toAlgebra
  let φ : F.obj i →ₐ[R] F.obj j :=
    { (F.map f).hom with commutes' := fun _ ↦ rfl }
  have hgen : (⊤ : Subalgebra R (F.obj i)) ≤ (⊥ : Subalgebra R (F.obj j)).comap φ := by
    rw [← hs]
    apply Algebra.adjoin_le
    intro x hx
    change φ x ∈ (⊥ : Subalgebra R (F.obj j))
    rw [Algebra.mem_bot]
    exact ⟨r ⟨x, hx⟩, hf ⟨x, hx⟩⟩
  refine ⟨j, f, ?_⟩
  intro z
  obtain ⟨x, rfl⟩ := htrans f z
  exact Algebra.mem_bot.mp (hgen (show x ∈ (⊤ : Subalgebra R (F.obj i)) from trivial))

end FLT.Mazur.Approximation
