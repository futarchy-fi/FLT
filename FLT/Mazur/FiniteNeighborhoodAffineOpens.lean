/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Affine chart preimages over an affine base neighborhood

If a morphism becomes finite after restricting the base, each affine target
chart has affine inverse image on that restriction. The base neighborhood
inclusion is affine, so restricting the chart preserves affineness too.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.Approximation

/-- Restriction over an affine open of an affine base has affine source inclusion. -/
theorem isAffineHom_baseOpen_inclusion {Y S : Scheme.{u}} [IsAffine S]
    (g : Y ⟶ S) (U : S.Opens) (hU : IsAffineOpen U) :
    IsAffineHom (g ⁻¹ᵁ U).ι := by
  let _ : IsAffine U.toScheme := hU
  let _ : IsAffineHom U.ι := inferInstance
  exact MorphismProperty.of_isPullback (isPullback_morphismRestrict g U)
    (inferInstance : IsAffineHom U.ι)

/-- A finite restriction has affine inverse images of the original affine target charts. -/
theorem isAffineOpen_chart_preimage_finite_restrict {X Y S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ Y) (g : Y ⟶ S) (U : S.Opens) (hU : IsAffineOpen U)
    [IsFinite (f ∣_ (g ⁻¹ᵁ U))] (C : Y.Opens) (hC : IsAffineOpen C) :
    IsAffineOpen ((f ⁻¹ᵁ (g ⁻¹ᵁ U)).ι ⁻¹ᵁ (f ⁻¹ᵁ C)) := by
  let _ := isAffineHom_baseOpen_inclusion g U hU
  have ha := (hC.preimage (g ⁻¹ᵁ U).ι).preimage (f ∣_ (g ⁻¹ᵁ U))
  have he := congrArg (fun k ↦ k ⁻¹ᵁ C) (morphismRestrict_ι f (g ⁻¹ᵁ U))
  simpa only [Scheme.Hom.comp_preimage] using (he ▸ ha)

end FLT.Mazur.Approximation
