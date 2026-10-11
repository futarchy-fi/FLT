/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertTestUnionLift
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Open representability of the glued Picard map

The base change of the glued Picard map by any original section is represented
by the actual open union on its test. This is a presheaf pullback, without any
surjectivity assumption on the chosen small family of translated charts.
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
  {ι : Type} (a : ι → TranslatedHilbertIndex f)
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- The original Picard-map base change is represented by the actual open union. -/
theorem translatedHilbertGluedPicardMap_isPullback :
    IsPullback (uliftYoneda.{1}.map (translatedHilbertTestUnionToGlued f hL a T s))
      (uliftYoneda.{1}.map (translatedHilbertTestUnionι f a T s))
      (translatedHilbertGluedPicardMap f hL a) (uliftYonedaEquiv.symm s) := by
  apply IsPullback.of_forall_isPullback_app
  intro U
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro q
    change translatedHilbertGluedPoint f hL a U.unop
      (q.down ≫ translatedHilbertTestUnionToGlued f hL a T s) =
        (relativeFppfSheaf f).obj.map (q.down ≫ translatedHilbertTestUnionι f a T s).op s
    rw [translatedHilbertGluedPoint_natural, translatedHilbertTestUnion_class]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  · intro q r hqr
    apply ULift.ext
    apply (cancel_mono (translatedHilbertTestUnionι f a T s)).mp
    exact congrArg ULift.down hqr.2
  · intro k b hkb
    obtain ⟨q, hq, _⟩ := translatedHilbertTestUnion_lift f hL a T s b.down k.down hkb
    exact ⟨ULift.up q, ULift.ext hq.2, ULift.ext hq.1⟩

/-- On any relative test, image membership is exactly factorization through the open union. -/
theorem translatedHilbertGluedPoint_mem_range_iff {U : Over (Spec (.of R))} (b : U ⟶ T) :
    (relativeFppfSheaf f).obj.map b.op s ∈ Set.range (translatedHilbertGluedPoint f hL a U) ↔
      ∃! q : U ⟶ translatedHilbertTestUnion f a T s,
        q ≫ translatedHilbertTestUnionι f a T s = b := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨q, hq, _⟩ := translatedHilbertTestUnion_lift f hL a T s b k hk
    exact ⟨q, hq.1, fun r hr ↦
      (cancel_mono (translatedHilbertTestUnionι f a T s)).mp (hr.trans hq.1.symm)⟩
  · rintro ⟨q, hq, _⟩
    refine ⟨q ≫ translatedHilbertTestUnionToGlued f hL a T s, ?_⟩
    rw [translatedHilbertGluedPoint_natural, translatedHilbertTestUnion_class,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hq]

end FLT.Mazur.HilbertChart
