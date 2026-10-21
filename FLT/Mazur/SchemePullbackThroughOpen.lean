/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Pullback geometry through an original target neighborhood

When the base map factors through an open of the original target, the whole
pullback is already the pullback of the original restricted morphism. Thus
local geometry on that neighborhood suffices for the entire new source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemePullbackThroughOpen
variable {X Y X' Y' : Scheme.{0}} {a : X' ⟶ X} {b : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (H : IsPullback a b f g)
  (U : Y.Opens) (k : Y' ⟶ U.toScheme) (hk : k ≫ U.ι = g)

/-- The whole pullback source maps to the preimage of the original neighborhood. -/
def sourceMap : X' ⟶ (f ⁻¹ᵁ U).toScheme :=
  (isPullback_morphismRestrict f U).lift (b ≫ k) a
    (by rw [Category.assoc, hk, H.w])

/-- The constructed source map retains the original source projection. -/
@[reassoc] theorem sourceMap_ι : sourceMap H U k hk ≫ (f ⁻¹ᵁ U).ι = a :=
  (isPullback_morphismRestrict f U).lift_snd _ _ _

/-- The source map commutes with the restricted original morphism. -/
@[reassoc] theorem sourceMap_restrict : sourceMap H U k hk ≫ f ∣_ U = b ≫ k :=
  (isPullback_morphismRestrict f U).lift_fst _ _ _

/-- The restricted original morphism has the same full pullback. -/
theorem isPullback : IsPullback (sourceMap H U k hk) b (f ∣_ U) k := by
  apply IsPullback.of_right _ (sourceMap_restrict H U k hk)
    (isPullback_morphismRestrict f U).flip
  rw [sourceMap_ι, hk]
  exact H

include H hk in
/-- Any property stable under base change transfers from this original neighborhood. -/
theorem property (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange]
    (hP : P (f ∣_ U)) : P b :=
  MorphismProperty.of_isPullback (isPullback H U k hk) hP

end FLT.Mazur.SchemePullbackThroughOpen
