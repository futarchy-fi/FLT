/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalAffineRefinement
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Detecting open immersions on principal refinements

For a map of affine schemes, principal opens pulled back from the target
are saturated on fibers. If these opens cover the source and each restricted
map is an open immersion, the original map is an open immersion too.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

/-- An open cover by fiber-saturated open immersions detects an open immersion. -/
theorem isOpenImmersion_of_saturated_cover {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type v} (U : I → Scheme.{u}) (j : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x, ∃ i, x ∈ Set.range (j i))
    (hsat : ∀ i, f ⁻¹' Set.range (j i ≫ f) ⊆ Set.range (j i))
    (hopen : ∀ i, IsOpenImmersion (j i ≫ f)) : IsOpenImmersion f := by
  have hinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨i, a, rfl⟩ := hcover x
    have hy : y ∈ Set.range (j i) := hsat i ⟨a, hxy⟩
    obtain ⟨b, rfl⟩ := hy
    let := hopen i
    have hab : a = b := (j i ≫ f).isOpenEmbedding.injective hxy
    exact congrArg (j i) hab
  apply IsOpenImmersion.of_forall_source_exists f hinj
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact ⟨U i, j i, inferInstance, hi, hopen i⟩

/-- Pulled-back principal charts detect an affine open immersion. -/
theorem isOpenImmersion_of_principal_refinements {R S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S) {I : Type v} (z : I → R)
    (hcover : (⨆ i, PrimeSpectrum.basicOpen (f (z i))) = ⊤)
    (hopen : ∀ i, IsOpenImmersion
      (PrincipalAffineRefinement.inclusion (f (z i)) ≫ Spec.map (CommRingCat.ofHom f))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom f)) := by
  apply isOpenImmersion_of_saturated_cover _
    (fun i ↦ Spec (.of (Localization.Away (f (z i)))))
    (fun i ↦ PrincipalAffineRefinement.inclusion (f (z i)))
  · intro x
    have hx : x ∈ (⨆ i, PrimeSpectrum.basicOpen (f (z i))) := by
      rw [hcover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine ⟨i, ?_⟩
    rw [PrincipalAffineRefinement.range_inclusion]
    exact hi
  · intro i y hy
    obtain ⟨a, ha⟩ := hy
    rw [PrincipalAffineRefinement.range_inclusion (f (z i))]
    have hx : PrincipalAffineRefinement.inclusion (f (z i)) a ∈
        PrimeSpectrum.basicOpen (f (z i)) := by
      change PrincipalAffineRefinement.inclusion (f (z i)) a ∈
        (PrimeSpectrum.basicOpen (f (z i)) : Set (PrimeSpectrum S))
      rw [← PrincipalAffineRefinement.range_inclusion (f (z i))]
      exact ⟨a, rfl⟩
    change (Spec.map (CommRingCat.ofHom f)
      (PrincipalAffineRefinement.inclusion (f (z i)) a)) ∈
        PrimeSpectrum.basicOpen (z i) at hx
    change (Spec.map (CommRingCat.ofHom f) y) ∈ PrimeSpectrum.basicOpen (z i)
    change Spec.map (CommRingCat.ofHom f)
      (PrincipalAffineRefinement.inclusion (f (z i)) a) =
        Spec.map (CommRingCat.ofHom f) y at ha
    exact ha ▸ hx
  · exact hopen

end FLT.Mazur.Approximation
