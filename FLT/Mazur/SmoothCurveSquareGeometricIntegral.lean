/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Geometric integrality of the original relative square

The first projection has geometrically integral fibers over an integral field
fiber of the original curve. Smooth flatness gives integrality of the square.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} (G : Over S) [Smooth G.hom] [GeometricallyIntegral G.hom]

/-- The actual relative square has integral fibers over every base field. -/
theorem smoothCurveSquare_geometricallyIntegral : GeometricallyIntegral (G ⊗ G).hom := by
  refine ⟨fun K _ g P p q H ↦ ?_⟩
  let F := Over.pullback g
  let G' := F.obj G
  let _ : Smooth G'.hom := inferInstanceAs (Smooth (pullback.snd G.hom g))
  let _ : GeometricallyIntegral G'.hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd G.hom g))
  let _ : IsIntegral G'.left := GeometricallyIntegral.isIntegral_of_subsingleton G'.hom
  let _ : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  let _ : IsIntegral (G' ⊗ G').left :=
    inferInstanceAs (IsIntegral (pullback G'.hom G'.hom : Scheme))
  let e : (G' ⊗ G').left ≅ pullback (G ⊗ G).hom g :=
    (Over.forget _).mapIso (Functor.Monoidal.μIso F G G)
  let _ : IsIntegral (pullback (G ⊗ G).hom g : Scheme) := IsIntegral.of_isIso e.hom
  exact IsIntegral.of_isIso H.isoPullback.inv

end FLT.Mazur.FCurve
