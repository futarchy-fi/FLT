/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Transport of relative smooth loci

Smoothness is unchanged by an isomorphism of the base. Together with the
open-immersion preimage formula, this transports smooth loci across
isomorphisms of arrows, including simultaneous changes of source and base.
-/

public section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicGeometry

universe u
variable {X Y Z X' Y' : Scheme.{u}}

/-- Changing the base by an isomorphism does not change the smooth locus. -/
theorem Scheme.Hom.smoothLocus_comp_isIso (f : X ⟶ Y) (e : Y ⟶ Z)
    [LocallyOfFinitePresentation f] [IsIso e] :
    (f ≫ e).smoothLocus = f.smoothLocus := by
  ext x
  change (Scheme.Hom.stalkMap (f ≫ e) x).hom.FormallySmooth ↔ _
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
    RingHom.FormallySmooth.respectsIso.cancel_left_isIso]
  rfl

/-- Smooth loci transport along an isomorphism of scheme arrows. -/
theorem Scheme.Hom.preimage_smoothLocus_arrowIso (f : X ⟶ Y) (g : X' ⟶ Y')
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]
    (e : Arrow.mk f ≅ Arrow.mk g) :
    e.hom.left ⁻¹ᵁ g.smoothLocus = f.smoothLocus := by
  rw [Scheme.Hom.preimage_smoothLocus_eq]
  have h : e.hom.left ≫ g = f ≫ e.hom.right := e.hom.w
  rw! [h]
  exact f.smoothLocus_comp_isIso e.hom.right

end AlgebraicGeometry
