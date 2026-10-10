/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NoetherianLocalClosedFiberFunctions
public import FLT.Mazur.ArtinianProperAffineBaseChange

/-!
# Noetherian local base changes at a connected closed fiber

A local test base has constant actual functions whenever its closed point maps
into the original geometric connectedness locus. The test morphism need not
be flat. Local coefficient homomorphisms preserve the required closed point.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.LocalClosedFiberBaseChange
open Approximation ArtinianProperAffineBaseChange AffineBaseChangeCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Actual functions after any Noetherian local test whose closed point has connected fiber. -/
theorem appTop_bijective {B : CommRingCat.{0}} [IsNoetherianRing B] [IsLocalRing B]
    {P X S : Scheme.{0}} {p : P ⟶ X} {q : P ⟶ Spec B}
    {f : X ⟶ S} {g : Spec B ⟶ S} (h : IsPullback p q f g)
    [IsProper f] [Flat f] [GeometricallyReduced f]
    (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    (hc : g (IsLocalRing.closedPoint B) ∈ geometricallyConnectedLocus f) :
    Function.Bijective q.appTop := by
  let _ : IsProper q := MorphismProperty.of_isPullback h inferInstance
  let _ : Flat q := MorphismProperty.of_isPullback h inferInstance
  let _ : GeometricallyReduced q := MorphismProperty.of_isPullback h inferInstance
  apply NoetherianLocalClosedFiberFunctions.appTop_bijective q
    (sectionOfSquare h s hs) (sectionOfSquare_projection h s hs)
  change IsLocalRing.closedPoint B ∈ geometricallyConnectedLocus q
  rwa [geometricallyConnectedLocus_of_isPullback h]

/-- A local coefficient homomorphism carries the closed point to the affine closed point. -/
theorem baseMap_closedPoint {S : Scheme} [IsAffine S] [IsLocalRing Γ(S, ⊤)]
    (B : Type) [CommRing B] [IsLocalRing B] [Algebra Γ(S, ⊤) B]
    [IsLocalHom (algebraMap Γ(S, ⊤) B)] :
    baseMap S B (IsLocalRing.closedPoint B) =
      S.isoSpec.inv (IsLocalRing.closedPoint Γ(S, ⊤)) := by
  rw [baseMap, Scheme.Hom.comp_apply, Spec_closedPoint]
  rfl

/-- Nonflat local coefficient base changes have the actual structural comparison. -/
theorem coefficient_appTop_bijective {X S : Scheme.{0}} [IsAffine S]
    [IsLocalRing Γ(S, ⊤)] (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyReduced f]
    (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    (hc : S.isoSpec.inv (IsLocalRing.closedPoint Γ(S, ⊤)) ∈ geometricallyConnectedLocus f)
    (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [Algebra Γ(S, ⊤) B] [IsLocalHom (algebraMap Γ(S, ⊤) B)] :
    Function.Bijective (pullback.snd f (baseMap S B)).appTop := by
  apply appTop_bijective (IsPullback.of_hasPullback f (baseMap S B)) s hs
  rwa [baseMap_closedPoint]

end FLT.Mazur.LocalClosedFiberBaseChange
