/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Pullback of an ambient scalar to an inverse-image chart

Restricting an ambient function to a chart and pulling it back on top
sections agrees with the original ambient structure-sheaf pullback.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The actual restricted scheme map pulls an ambient scalar back on its image open. -/
theorem morphismRestrict_top_restrict {X Y : Scheme.{u}} (p : X ⟶ Y) (U : Y.Opens)
    (r : Γ(Y, U)) :
    (p ∣_ U).appTop (Y.presheaf.map (homOfLE (U.ι_image_le ⊤)).op r) =
      p.appLE U ((p ⁻¹ᵁ U).ι ''ᵁ ⊤) ((p ⁻¹ᵁ U).ι_image_le ⊤) r := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, morphismRestrict_appLE]
  erw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rfl

end FLT.Mazur.Approximation
