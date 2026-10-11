/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedPointStalkMap

/-!
# Germs under composite specified-point stalk maps

Composition on germs can be proved before instantiating a large glued scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.ClosedPointStalkMap

set_option backward.isDefEq.respectTransparency false

/-- At the literal image point the specified-point map is the original stalk map. -/
theorem pointMap_image {X Y : Scheme} (f : X ⟶ Y) (x : X) :
    pointMap f x (f x) rfl = f.stalkMap x := rfl

/-- A composite specified-point stalk map retains the actual pullback of each section. -/
theorem pointMap_comp_germ {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) (z : Z) (hz : (f ≫ g) x = z) (U : Z.Opens) (hu : z ∈ U)
    (hx : g (f x) ∈ U) (a : Γ(Z, U)) :
    pointMap (f ≫ g) x z hz (Z.presheaf.germ U z hu a) =
      f.stalkMap x (Y.presheaf.germ (g ⁻¹ᵁ U) (f x) hx (g.app U a)) := by
  rw [← pointMap_comp f g x (f x) z rfl hz, CommRingCat.comp_apply, pointMap_image]
  have he := pointMap_germ g (f x) z hz U (g ⁻¹ᵁ U) le_rfl hx hu a
  rw [Scheme.Hom.appLE_eq_app] at he
  exact congrArg (f.stalkMap x) he

end FLT.Mazur.ClosedPointStalkMap
