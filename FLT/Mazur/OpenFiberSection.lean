/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Open sections in a scheme fiber

A section which is the entire fiber on an actual source open gives an open
immersion into the full scheme-theoretic fiber. This keeps the original maps.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.OpenFiberSection

universe u
variable {U X Y S : Scheme.{u}} (j : U ⟶ X) (f : X ⟶ Y) (z : S ⟶ Y)
  (e : S ⟶ U) (k : S ⟶ pullback f z)
  (he : e ≫ j = k ≫ pullback.fst f z) (hk : k ≫ pullback.snd f z = 𝟙 S)
  (H : IsPullback e (𝟙 S) (j ≫ f) z)

include he hk H
/-- The local fiber point is the actual inverse image of the source open in the full fiber. -/
theorem isPullback : IsPullback e k j (pullback.fst f z) := by
  have h : IsPullback e (k ≫ pullback.snd f z) (j ≫ f) z := by rwa [hk]
  exact h.of_bot he (IsPullback.of_hasPullback f z)

/-- Local exactness of the section makes it an open immersion into the original full fiber. -/
theorem isOpenImmersion [IsOpenImmersion j] : IsOpenImmersion k :=
  MorphismProperty.of_isPullback (isPullback j f z e k he hk H) inferInstance

end FLT.Mazur.OpenFiberSection
