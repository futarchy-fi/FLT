/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalTargetRefinement
public import FLT.Mazur.PrincipalLocalizationPullback
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Isomorphisms on principal target refinements

An affine open immersion restricts to an isomorphism above any principal
target open contained in its image. The map is the explicit localization
restriction and its square remains the specified localization pullback.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

open PrincipalAffineRefinement LocalizationJointRestriction

/-- Restriction to a principal target open contained in the image is an isomorphism. -/
theorem principalTargetRestriction_isIso {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))] (r : R)
    (hr : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆
      Set.range (Spec.map (CommRingCat.ofHom f))) :
    IsIso (Spec.map (CommRingCat.ofHom (restriction f r))) := by
  let g := Spec.map (CommRingCat.ofHom (restriction f r))
  have hp := PrincipalLocalizationPullback.isPullback f r
  have : IsOpenImmersion g := IsOpenImmersion.of_isPullback hp inferInstance
  have hsurj : Function.Surjective g := by
    intro y
    have hy : inclusion r y ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← range_inclusion]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hr hy
    obtain ⟨a, _, ha⟩ := Scheme.exists_preimage_of_isPullback hp x y hx
    exact ⟨a, ha⟩
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top g
  apply TopologicalSpace.Opens.ext
  exact Set.range_eq_univ.mpr hsurj

/-- Every affine open immersion has finite principal restrictions that are
actual isomorphisms, with their source cover retained. -/
theorem exists_finite_principal_target_isomorphisms {R S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))] :
    ∃ t : Finset R, (⨆ i : t, PrimeSpectrum.basicOpen (f i)) = ⊤ ∧
      ∀ r ∈ t, IsIso (Spec.map (CommRingCat.ofHom (restriction f r))) := by
  obtain ⟨t, hcover, ht⟩ := exists_finite_principal_target_refinement f
  exact ⟨t, hcover, fun r hr ↦ principalTargetRestriction_isIso f r (ht r hr)⟩

/-- The canonical localized ring map is bijective on each such target open. -/
theorem principalTargetRestriction_bijective {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))] (r : R)
    (hr : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆
      Set.range (Spec.map (CommRingCat.ofHom f))) : Function.Bijective (restriction f r) := by
  let F := CommRingCat.ofHom (restriction f r)
  have : IsIso (Scheme.Spec.map F.op) := principalTargetRestriction_isIso f r hr
  have : IsIso F.op := isIso_of_reflects_iso F.op Scheme.Spec
  have : IsIso F := isIso_of_op F
  exact ConcreteCategory.bijective_of_isIso F

end FLT.Mazur.Approximation
