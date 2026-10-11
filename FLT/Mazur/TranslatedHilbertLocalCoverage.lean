/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertCoverageCriterion
public import FLT.Mazur.TranslatedHilbertGluedImageDescent

/-!
# Fppf locality of coverage by the actual translated intersections

For a fixed chosen family, covering every point of the original test can be
checked after any fppf cover. Local representatives descend as scheme morphisms,
so no choice of one global chart or one global line representative is needed.
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
  {κ : Type} (V : κ → Over (Spec (.of R))) (c : ∀ i, V i ⟶ T)
  (hc : Sieve.ofArrows V c ∈ (Scheme.fppfTopology.over (Spec (.of R))) T)

include hL hc

/-- Membership in the original image is equivalent to membership on any fppf cover. -/
theorem translatedHilbertGluedPoint_exists_iff_fppf :
    (∃ k : T ⟶ translatedHilbertGluedTest f hL a, translatedHilbertGluedPoint f hL a T k = s) ↔
      ∀ i, ∃ p : V i ⟶ translatedHilbertGluedTest f hL a,
        translatedHilbertGluedPoint f hL a (V i) p = (relativeFppfSheaf f).obj.map (c i).op s := by
  constructor
  · rintro ⟨k, hk⟩ i
    exact ⟨c i ≫ k, (translatedHilbertGluedPoint_natural f hL a (c i) k).trans
      (congrArg ((relativeFppfSheaf f).obj.map (c i).op) hk)⟩
  · intro h
    choose p hp using h
    obtain ⟨k, hk, _⟩ := translatedHilbertGluedPoint_of_fppf_image f hL a T s V c hc p hp
    exact ⟨k, hk⟩

/-- Actual chart-test intersections cover globally exactly when they cover fppf locally. -/
theorem translatedHilbertTestUnion_cover_iff_fppf :
    (∀ x : T.left, ∃ i, ∃ y : (translatedHilbertOverlapTest f (a i).1 (a i).2 T s).left,
      (translatedHilbertOverlapArrow f (a i).1 (a i).2 T s).left y = x) ↔
    ∀ j, ∀ x : (V j).left, ∃ i,
      ∃ y : (translatedHilbertOverlapTest f (a i).1 (a i).2 (V j)
        ((relativeFppfSheaf f).obj.map (c j).op s)).left,
      (translatedHilbertOverlapArrow f (a i).1 (a i).2 (V j)
        ((relativeFppfSheaf f).obj.map (c j).op s)).left y = x := by
  rw [← translatedHilbertGluedPoint_exists_iff_cover f hL a T s,
    translatedHilbertGluedPoint_exists_iff_fppf f hL a T s V c hc]
  exact forall_congr' fun j ↦ translatedHilbertGluedPoint_exists_iff_cover f hL a (V j)
    ((relativeFppfSheaf f).obj.map (c j).op s)

/-- The representing open inclusion is an isomorphism precisely when it is so fppf locally. -/
theorem translatedHilbertTestUnion_isIso_iff_fppf :
    IsIso (translatedHilbertTestUnionι f a T s) ↔
      ∀ j, IsIso (translatedHilbertTestUnionι f a (V j)
        ((relativeFppfSheaf f).obj.map (c j).op s)) := by
  rw [← translatedHilbertGluedPoint_exists_iff_isIso f hL a T s,
    translatedHilbertGluedPoint_exists_iff_fppf f hL a T s V c hc]
  exact forall_congr' fun j ↦ translatedHilbertGluedPoint_exists_iff_isIso f hL a (V j)
    ((relativeFppfSheaf f).obj.map (c j).op s)

end FLT.Mazur.HilbertChart
