/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedIntegerChartComparison
public import FLT.Mazur.PrincipalTargetRestrictionIsomorphism

/-!
# A finite algebraic criterion for affine open immersions

An affine map is an open immersion exactly when finitely many target
denominators cover its source and the corresponding canonical localization
maps are bijective. This isolates finite algebraic data for overlap descent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

open LocalizationJointRestriction

/-- Covering localized ring equivalences certify an affine open immersion. -/
theorem isOpenImmersion_of_localized_bijective {R S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S) {I : Type v} (z : I → R)
    (hcover : (⨆ i, PrimeSpectrum.basicOpen (f (z i))) = ⊤)
    (hlocal : ∀ i, Function.Bijective (restriction f (z i))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom f)) := by
  apply isOpenImmersion_of_principal_refinements f z hcover
  intro i
  exact localizedComparison_chart_isOpenImmersion f (z i) (f (z i))
    (RingEquiv.ofBijective (restriction f (z i)) (hlocal i))
    (restriction_algebraMap f (z i))

/-- Affine open immersion is equivalent to finite principal cover and
bijectivity data for the canonical localized restrictions. -/
theorem isOpenImmersion_iff_finite_localized_bijective {R S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom f)) ↔
      ∃ t : Finset R, (⨆ i : t, PrimeSpectrum.basicOpen (f i)) = ⊤ ∧
        ∀ r ∈ t, Function.Bijective (restriction f r) := by
  constructor
  · intro hf
    let := hf
    obtain ⟨t, hcover, ht⟩ := exists_finite_principal_target_refinement f
    exact ⟨t, hcover, fun r hr ↦ principalTargetRestriction_bijective f r (ht r hr)⟩
  · rintro ⟨t, hcover, ht⟩
    exact isOpenImmersion_of_localized_bijective f (fun i : t ↦ (i : R))
      hcover (fun i ↦ ht i i.property)

end FLT.Mazur.Approximation
