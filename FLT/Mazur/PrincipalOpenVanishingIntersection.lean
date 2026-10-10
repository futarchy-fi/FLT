/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# A vanishing function has empty intersection with its principal open

A ring map killing the localized function gives the empty scheme as the
entire fiber product with the principal open, without a reducedness hypothesis.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.PrincipalOpenVanishingIntersection
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (x : A)
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x)))
local notation "g" => Spec.map (CommRingCat.ofHom f)

/-- Restriction to an affine scheme pulls back the entire principal-open image. -/
theorem preimage : g ⁻¹' Set.range i = (PrimeSpectrum.basicOpen (f x) : Set (PrimeSpectrum B)) := by
  change PrimeSpectrum.comap f ⁻¹' Set.range
    (PrimeSpectrum.comap (algebraMap A (Localization.Away x))) = _
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away x) x]
  rfl

/-- Killing the localized function excludes every point of that principal open. -/
theorem disjoint (hx : f x = 0) : Disjoint (Set.range i) (Set.range g) := by
  rw [Set.disjoint_left]
  rintro _ hi ⟨z, rfl⟩
  have hz : z ∈ (PrimeSpectrum.basicOpen (f x) : Set (PrimeSpectrum B)) := by
    rw [← preimage f x]
    exact hi
  simp only [hx, PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.coe_bot,
    Set.mem_empty_iff_false] at hz

/-- The entire scheme intersection is empty, including all scheme structure. -/
theorem isPullback (hx : f x = 0) :
    IsPullback (Scheme.emptyTo (Spec (.of (Localization.Away x))))
      (Scheme.emptyTo (Spec (.of B))) i g := by
  let _ := Scheme.isEmpty_pullback i g (disjoint f x hx)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback i g)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end FLT.Mazur.PrincipalOpenVanishingIntersection
