/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Constructible images after a Noetherian base change

A finite-type image becomes constructible after pulling it back to a
Noetherian test scheme. The original target need not be Noetherian.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
namespace FLT.Mazur.SchemeConstructibleNoetherianPullback
variable {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
  [LocallyOfFiniteType f] [QuasiCompact f] [IsNoetherian Y]

/-- Base change proves constructibility over the test scheme without changing the image. -/
theorem preimage_image_constructible (S : Set X) (hS : IsConstructible S) :
    IsConstructible (g ⁻¹' (f '' S)) := by
  have h := (pullback.snd f g).isConstructible_image
    ((pullback.fst f g).isConstructible_preimage hS)
  rwa [Scheme.image_preimage_eq_of_isPullback (IsPullback.of_hasPullback f g)] at h

/-- The actual finite-type image pulls back to a constructible set on every Noetherian test. -/
theorem preimage_range_constructible : IsConstructible (g ⁻¹' Set.range f) := by
  simpa only [Set.image_univ] using preimage_image_constructible f g Set.univ .univ

end FLT.Mazur.SchemeConstructibleNoetherianPullback
