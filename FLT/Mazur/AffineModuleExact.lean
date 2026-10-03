/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentSubquotient

/-!
# Detecting exactness of affine module sheaves on global sections

For modules reconstructed by tilde, the natural counit transports a short exact
sequence of global sections to the actual module sheaves.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.AffineModuleExact
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
/-- Taking global sections of spectrum modules is additive. -/
instance {R : CommRingCat.{u}} : (moduleSpecΓFunctor (R := R)).Additive where
  map_add := rfl
variable {R : CommRingCat.{u}} (S : ShortComplex (Spec R).Modules)
  [IsIso S.X₁.fromTildeΓ] [IsIso S.X₂.fromTildeΓ] [IsIso S.X₃.fromTildeΓ]
/-- The tilde counit compares a complex with its global-section reconstruction. -/
def comparison :
    (S.map moduleSpecΓFunctor).map (tilde.functor R) ≅ S :=
  ShortComplex.isoMk (asIso S.X₁.fromTildeΓ) (asIso S.X₂.fromTildeΓ)
    (asIso S.X₃.fromTildeΓ)
    (fromTildeΓNatTrans.naturality S.f).symm (fromTildeΓNatTrans.naturality S.g).symm
/-- Exactness of global sections implies exactness of these affine module sheaves. -/
theorem shortExact_of_sections (h : (S.map moduleSpecΓFunctor).ShortExact) :
    S.ShortExact :=
  ShortComplex.shortExact_of_iso (comparison S)
    (FCurve.CoherentDevissage.coherentTilde_shortExact h)
end FLT.Mazur.AffineModuleExact
