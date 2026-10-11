/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertFullLift

/-!
# Original full chart intersections are exact preimages in the full union

Pulling the constructed full intersection back along an original Hilbert chart
recovers that chart's original full intersection, with its independent base
coordinate. The equality follows from the universal properties on every test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (V : Over (Spec (.of R))) {ι : Type} (a : ι → BaseMarkedHilbertIndex f V)
  (U : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op U)) (i : ι)

/-- Lifts along an original chart recover the original full chart intersection uniquely. -/
theorem baseMarkedFull_chart_lift {W : Over (Spec (.of R))}
    (q : W ⟶ baseMarkedFullIntersection f V a U s)
    (k : W ⟶ variableHilbertTest f (a i).1 V)
    (he : q ≫ baseMarkedFullToGlued f hL V a U s = k ≫ baseMarkedGluedArrow f hL V a i) :
    ∃! l : W ⟶ variableHilbertOverlap f (a i).1 V (a i).2 U s,
      l ≫ baseMarkedFullChart f V a U s i = q ∧
        l ≫ variableHilbertOverlapToChart f (a i).1 hL V (a i).2 U s = k := by
  have hc : variableHilbertPoint f (a i).1 hL V (a i).2 W k =
      (relativeFppfSheaf f).obj.map (q ≫ baseMarkedFullToTest f V a U s).op s := by
    rw [← baseMarkedGluedPoint_chart, ← he, baseMarkedGluedPoint_natural,
      baseMarkedFullToGlued_class]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  obtain ⟨l, hl, _⟩ := variableHilbertOverlap_lift f (a i).1 hL V (a i).2 U s
    (q ≫ baseMarkedFullToTest f V a U s) k hc
  have hq : l ≫ baseMarkedFullChart f V a U s i = q := by
    apply baseMarkedFull_hom_ext f hL V a U s
    · rw [Category.assoc, baseMarkedFullChart_toTest]
      exact hl.1
    · rw [Category.assoc, baseMarkedFullChart_toGlued, ← Category.assoc, hl.2]
      exact he.symm
  refine ⟨l, ⟨hq, hl.2⟩, ?_⟩
  intro m hm
  apply variableHilbertOverlap_hom_ext f (a i).1 hL V (a i).2 U s
  · simpa only [Category.assoc, baseMarkedFullChart_toTest] using
      congrArg (fun r ↦ r ≫ baseMarkedFullToTest f V a U s) (hm.1.trans hq.symm)
  · exact hm.2.trans hl.2.symm

/-- This is a scheme-theoretic pullback of the actual original full chart intersection. -/
theorem baseMarkedFull_chart_isPullback :
    IsPullback (baseMarkedFullChart f V a U s i)
      (variableHilbertOverlapToChart f (a i).1 hL V (a i).2 U s)
      (baseMarkedFullToGlued f hL V a U s) (baseMarkedGluedArrow f hL V a i) := by
  let lift (z : PullbackCone (baseMarkedFullToGlued f hL V a U s)
      (baseMarkedGluedArrow f hL V a i)) :=
    baseMarkedFull_chart_lift f hL V a U s i z.fst z.snd z.condition
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (baseMarkedFullChart_toGlued f hL V a U s i) (fun z ↦ (lift z).choose)
    (fun z ↦ (lift z).choose_spec.1.1) (fun z ↦ (lift z).choose_spec.1.2)
    (fun z q hq ht ↦ (lift z).choose_spec.2 q ⟨hq, ht⟩))

end FLT.Mazur.HilbertChart
