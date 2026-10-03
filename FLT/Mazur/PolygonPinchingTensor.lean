/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonPinchingFlatBaseChange
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Tensoring the pinching pushout

Pullback symmetry transports flat base change to the chosen monoidal product
in schemes over the coefficient field.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
universe u
namespace FLT.Mazur.PolygonPinchingTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {B : Scheme.{u}} (X Y : Over B)
/-- Compare the chosen tensor product with pullback followed by postcomposition. -/
def comparison : X ⊗ Y ≅ ((Over.pullback X.hom) ⋙ Over.map X.hom).obj Y :=
  (Over.map X.hom).mapIso (PinchingPullbackTransport.swap X.hom Y)
@[reassoc] theorem comparison_naturality {Y Z : Over B} (f : Y ⟶ Z) :
    X ◁ f ≫ (comparison X Z).hom =
      (comparison X Y).hom ≫ ((Over.pullback X.hom) ⋙ Over.map X.hom).map f := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;> simp [comparison, Over.pullback, PinchingPullbackTransport.swap]
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
variable (X : Over (Spec (.of K))) [Flat X.hom]
theorem isPushout {C : Over (Spec (.of K))}
    (p : PolygonPinching.components K n ⟶ C) (q : PolygonPinching.nodes K n ⟶ C)
    (h : IsPushout (PolygonPinching.toComponents K n hn) (PolygonPinching.toNodes K n) p q) :
    IsPushout (X ◁ PolygonPinching.toComponents K n hn) (X ◁ PolygonPinching.toNodes K n)
      (X ◁ p) (X ◁ q) := by
  have hp := (PolygonPinchingFlatBaseChange.pinching_pullback K n X.hom hn p q h).map
    (Over.map X.hom)
  exact hp.of_iso' (comparison X _) (comparison X _) (comparison X _) (comparison X _)
    (comparison_naturality X _).symm (comparison_naturality X _).symm
    (comparison_naturality X _).symm (comparison_naturality X _).symm
end FLT.Mazur.PolygonPinchingTensor
