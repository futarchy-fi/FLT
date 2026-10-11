/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertFullLift

/-!
# Full representability of the glued chart map to the original Picard sheaf

The constructed open union represents the entire test fiber product.
This compares original Picard classes with independent translation-base maps;
it is not a fiber product for only the same-base relation.
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
  (U : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op U))

/-- The full constructed intersection is the original Picard-presheaf pullback. -/
theorem baseMarkedGluedPicardMap_full_isPullback :
    IsPullback (uliftYoneda.{1}.map (baseMarkedFullToGlued f hL V a U s))
      (uliftYoneda.{1}.map (baseMarkedFullToTest f V a U s))
      (baseMarkedGluedPicardMap f hL V a) (uliftYonedaEquiv.symm s) := by
  apply IsPullback.of_forall_isPullback_app
  intro W
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro q
    change baseMarkedGluedPoint f hL V a W.unop
      (q.down ≫ baseMarkedFullToGlued f hL V a U s) =
        (relativeFppfSheaf f).obj.map (q.down ≫ baseMarkedFullToTest f V a U s).op s
    rw [baseMarkedGluedPoint_natural, baseMarkedFullToGlued_class]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  · intro q r hqr
    apply ULift.ext
    exact baseMarkedFull_hom_ext f hL V a U s
      (congrArg ULift.down hqr.2) (congrArg ULift.down hqr.1)
  · intro k b hkb
    obtain ⟨q, hq, _⟩ := baseMarkedFull_lift f hL V a U s b.down k.down hkb
    exact ⟨ULift.up q, ULift.ext hq.2, ULift.ext hq.1⟩

end FLT.Mazur.HilbertChart
