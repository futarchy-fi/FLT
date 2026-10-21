/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAdicVanishingOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Exact zero-germ loci under flat pullback

Flat local stalk maps are faithfully flat. Thus pullback preserves and reflects
actual zero germs, including nilpotents. No surjectivity of the scheme map is
needed to reflect a germ at a point in its image.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeAdicVanishingNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme} (f : X ⟶ Y) [Flat f]

/-- Flatness reflects sections of the local ring at every actual source point. -/
theorem flat_stalkMap_injective (x : X) : Function.Injective (f.stalkMap x) := by
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

/-- A pulled-back global section has zero germ exactly where the original one does. -/
theorem flat_germ_appTop_eq_zero_iff (a : Γ(Y, ⊤)) (x : X) :
    X.presheaf.germ ⊤ x (by trivial) (f.appTop a) = 0 ↔
      Y.presheaf.germ ⊤ (f x) (by trivial) a = 0 := by
  have he : f.stalkMap x (Y.presheaf.germ ⊤ (f x) (by trivial) a) =
      X.presheaf.germ ⊤ x (by trivial) (f.appTop a) := by
    simp [Scheme.Hom.appTop]
  rw [← he, ← map_zero (f.stalkMap x).hom]
  exact (flat_stalkMap_injective f x).eq_iff

/-- Flat pullback commutes with the full scheme-theoretic vanishing open. -/
theorem flat_vanishingOpen_preimage (a : Γ(Y, ⊤)) :
    vanishingOpen (f.appTop a) = f ⁻¹ᵁ vanishingOpen a := by
  ext x
  exact flat_germ_appTop_eq_zero_iff f a x

/-- Vanishing on any actual branch open gives original zero germs at its image points. -/
theorem flat_image_le_vanishingOpen (a : Γ(Y, ⊤)) (V : X.Opens)
    (hV : X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op (f.appTop a) = 0) :
    f '' (V : Set X) ⊆ vanishingOpen a := by
  rintro _ ⟨x, hx, rfl⟩
  exact (flat_germ_appTop_eq_zero_iff f a x).mp (le_vanishingOpen _ V hV hx)

end FLT.Mazur.SchemeAdicVanishingNeighborhood
