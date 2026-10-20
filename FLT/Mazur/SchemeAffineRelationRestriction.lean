/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Affine endpoint neighborhoods in a scheme relation

Over an affine base, the simultaneous inverse image of two affine endpoint
opens in a fiber product is affine. An affine relation over that product
therefore remains affine after restricting both endpoints.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeAffineRelationRestriction
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsAffine S]

/-- The simultaneous restriction of a fiber product to affine endpoint opens is affine. -/
theorem isAffineOpen_pullback_inf {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
  let _ : IsAffine U.toScheme := hU
  let _ : IsAffine V.toScheme := hV
  let p : pullback (U.ι ≫ f) (V.ι ≫ g) ⟶ pullback f g :=
    pullback.map _ _ _ _ U.ι V.ι (𝟙 S) (by simp) (by simp)
  convert isAffineOpen_opensRange p using 1
  apply Opens.ext
  simp only [Scheme.Hom.coe_opensRange, p, Scheme.Pullback.range_map,
    Scheme.Opens.range_ι]
  rfl

/-- An affine relation retains affineness on simultaneous affine endpoint neighborhoods. -/
theorem isAffineOpen_relation {R : Scheme.{u}} (a : R ⟶ pullback f g) [IsAffineHom a]
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen ((a ≫ pullback.fst f g) ⁻¹ᵁ U ⊓
      (a ≫ pullback.snd f g) ⁻¹ᵁ V) := by
  have h := (isAffineOpen_pullback_inf f g hU hV).preimage a
  simpa only [Scheme.Hom.preimage_inf, Scheme.Hom.comp_preimage] using h

end FLT.Mazur.SchemeAffineRelationRestriction
