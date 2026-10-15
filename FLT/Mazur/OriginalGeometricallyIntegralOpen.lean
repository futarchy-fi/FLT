/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Original nonempty open charts remain geometrically integral

Over a field, a nonempty original open meets every scalar fiber. Its scalar
extensions are nonempty open subschemes of the integral extended scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OriginalGeometricallyIntegralOpen
set_option backward.isDefEq.respectTransparency false
variable {k : Type} [Field k] {U X : Scheme}
  (i : U ⟶ X) [IsOpenImmersion i] [Nonempty U]
  (f : X ⟶ Spec (.of k)) [GeometricallyIntegral f]

/-- Geometric integrality holds for every nonempty original open chart over the field. -/
theorem geometricallyIntegral : GeometricallyIntegral (i ≫ f) := by
  constructor
  intro K _ t Y a b H
  let j : pullback (i ≫ f) t ⟶ pullback f t :=
    pullback.map _ _ _ _ i (𝟙 _) (𝟙 _) (by simp) (by simp)
  let _ : IsIntegral (pullback f t) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)
  let _ : IsIntegral (pullback (i ≫ f) t) := isIntegral_of_isOpenImmersion j
  exact IsIntegral.of_isIso H.isoPullback.inv

end FLT.Mazur.OriginalGeometricallyIntegralOpen
