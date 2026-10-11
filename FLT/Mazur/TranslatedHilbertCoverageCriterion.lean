/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertGluedOpen

/-!
# Exact coverage criterion for a chosen translated Hilbert family

An original section has a global representative precisely when its actual chart
intersections cover the test. This identifies the geometric existence problem
without assuming that a fixed small family of global translations is sufficient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  {ι : Type} (a : ι → TranslatedHilbertIndex f)
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- A global representative exists exactly when the original intersections cover every point. -/
theorem translatedHilbertGluedPoint_exists_iff_cover :
    (∃ k : T ⟶ translatedHilbertGluedTest f hL a, translatedHilbertGluedPoint f hL a T k = s) ↔
      ∀ x : T.left, ∃ i, ∃ y : (translatedHilbertOverlapTest f (a i).1 (a i).2 T s).left,
        (translatedHilbertOverlapArrow f (a i).1 (a i).2 T s).left y = x := by
  constructor
  · rintro ⟨k, hk⟩ x
    have he : translatedHilbertGluedPoint f hL a T k =
        (relativeFppfSheaf f).obj.map (𝟙 T).op s := by simpa using hk
    have hx := translatedHilbertTestUnion_range f hL a T s (𝟙 T) k he ⟨x, rfl⟩
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  · intro h
    have hc : Sieve.ofArrows (fun i ↦ translatedHilbertOverlapTest f (a i).1 (a i).2 T s)
        (fun i ↦ translatedHilbertOverlapArrow f (a i).1 (a i).2 T s) ∈
        (Scheme.fppfTopology.over (Spec (.of R))) T := by
      rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      apply Precoverage.generate_mem_toGrothendieck
      apply Scheme.zariskiPrecoverage_le_fppfPrecoverage
      exact (Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) ι
        (fun i ↦ (translatedHilbertOverlapTest f (a i).1 (a i).2 T s).left)
        (fun i ↦ (translatedHilbertOverlapArrow f (a i).1 (a i).2 T s).left) h).mem₀
    obtain ⟨k, hk, _⟩ := translatedHilbertGluedPoint_of_fppf_charts f hL a T s
      (fun i ↦ translatedHilbertOverlapTest f (a i).1 (a i).2 T s)
      (fun i ↦ translatedHilbertOverlapArrow f (a i).1 (a i).2 T s) hc id
      (fun i ↦ translatedHilbertOverlapToParameter f (a i).1 hL (a i).2 T s)
      (fun i ↦ translatedHilbertOverlap_class f (a i).1 hL (a i).2 T s)
    exact ⟨k, hk⟩

/-- Global representability is equivalent to the actual open inclusion being an isomorphism. -/
theorem translatedHilbertGluedPoint_exists_iff_isIso :
    (∃ k : T ⟶ translatedHilbertGluedTest f hL a, translatedHilbertGluedPoint f hL a T k = s) ↔
      IsIso (translatedHilbertTestUnionι f a T s) := by
  constructor
  · rintro ⟨k, hk⟩
    have he : translatedHilbertGluedPoint f hL a T k =
        (relativeFppfSheaf f).obj.map (𝟙 T).op s := by simpa using hk
    obtain ⟨q, hq, _⟩ := translatedHilbertTestUnion_lift f hL a T s (𝟙 T) k he
    refine ⟨⟨q, ?_, hq.1⟩⟩
    apply (cancel_mono (translatedHilbertTestUnionι f a T s)).mp
    rw [Category.assoc, hq.1, Category.comp_id, Category.id_comp]
  · intro h
    let _ := h
    refine ⟨inv (translatedHilbertTestUnionι f a T s) ≫
      translatedHilbertTestUnionToGlued f hL a T s, ?_⟩
    rw [translatedHilbertGluedPoint_natural, translatedHilbertTestUnion_class,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, IsIso.inv_hom_id]
    simp

end FLT.Mazur.HilbertChart
