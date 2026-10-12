/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# From a relative comparison to its fibers over the target

If a comparison becomes an isomorphism after a base test, pulling it back
along a point of the target on that test again gives an isomorphism. Both
maps are the categorical pullbacks of the original morphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve

set_option backward.isDefEq.respectTransparency false
universe u

/-- An isomorphic relative comparison remains isomorphic over each lifted target test. -/
theorem relativeComparison_pullback_isIso {S X Y T : Scheme.{u}}
    (q : X ⟶ S) (r : Y ⟶ S) (f : X ⟶ Y) (hf : f ≫ r = q) (a : T ⟶ Y)
    [IsIso (pullback.map q (a ≫ r) r (a ≫ r) f (𝟙 _) (𝟙 _)
      (by simpa using hf.symm) (by simp))] : IsIso (pullback.snd f a) := by
  let b := a ≫ r
  let g : pullback q b ⟶ pullback r b :=
    pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simpa using hf.symm) (by simp)
  have h : IsPullback (pullback.fst q b) g f (pullback.fst r b) := by
    apply IsPullback.of_bot (h₃₁ := b) _ (by simp [g]) (.of_hasPullback r b)
    simpa [hf, g] using
      (IsPullback.of_hasPullback q b)
  let t : T ⟶ pullback r b := pullback.lift a (𝟙 _) (by simp [b])
  have ht : t ≫ pullback.fst r b = a := by simp [t]
  have ha : IsPullback (pullback.fst f a) (pullback.snd f a) f
      (t ≫ pullback.fst r b) := by
    rw [ht]
    exact .of_hasPullback f a
  exact (ha.of_right' h).isIso_snd_of_isIso

end FLT.Mazur.FCurve
