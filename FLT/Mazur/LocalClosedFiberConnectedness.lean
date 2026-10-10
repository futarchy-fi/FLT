/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalClosedFiberUniversalFunctions

/-!
# Geometric connectedness from the local closed fiber

Universal affine function comparison proves geometric connectedness of the
whole pointed proper flat family from its closed fiber over a Noetherian
local affine base. All fibers are assumed geometrically reduced.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- One geometrically connected closed fiber controls the entire local family. -/
theorem geometricallyConnected_of_local_closedFiber {X S : Scheme.{0}} [IsAffine S]
    [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyReduced f]
    (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    (hc : S.isoSpec.inv (IsLocalRing.closedPoint Γ(S, ⊤)) ∈ geometricallyConnectedLocus f) :
    GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ a ↦ ?_⟩
  let q := pullback.snd f a
  have hb := LocalClosedFiberUniversalFunctions.appTop_bijective
    (IsPullback.of_hasPullback f a) s hs hc
  have : IsIso q.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hb
  have : IsDomain Γ(pullback f a, ⊤) :=
    (asIso q.appTop).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have := preconnectedSpace_of_globalSections_domain (pullback f a)
  let t := SchemeProperGeometricFiberSections.baseChangedSection f s hs a
  exact ⟨⟨t (Classical.arbitrary (Spec (.of K)))⟩⟩

/-- Ordinary connectedness of the actual local closed fiber is sufficient. -/
theorem geometricallyConnected_of_local_connected_closedFiber {X S : Scheme.{0}}
    [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyReduced f]
    (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    [ConnectedSpace (f.fiber (S.isoSpec.inv (IsLocalRing.closedPoint Γ(S, ⊤))))] :
    GeometricallyConnected f :=
  geometricallyConnected_of_local_closedFiber f s hs
    (mem_locus_of_connected_reduced_fiber f s hs _)

/-- The spectrum formulation uses the original local ring and its original closed point. -/
theorem geometricallyConnected_of_spec_local_closedFiber
    {R : CommRingCat.{0}} [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{0}} (f : X ⟶ Spec R) [IsProper f] [Flat f] [GeometricallyReduced f]
    (s : Spec R ⟶ X) (hs : s ≫ f = 𝟙 _)
    (hc : IsLocalRing.closedPoint R ∈ geometricallyConnectedLocus f) :
    GeometricallyConnected f := by
  let _ : IsLocalRing Γ(Spec R, ⊤) :=
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.isLocalRing
  let _ : IsNoetherianRing Γ(Spec R, ⊤) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  apply geometricallyConnected_of_local_closedFiber f s hs
  simpa only [Scheme.isoSpec_Spec_inv, Spec_closedPoint] using hc

end FLT.Mazur.Approximation
