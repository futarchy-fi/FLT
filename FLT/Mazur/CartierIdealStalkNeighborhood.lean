/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealStalkDescent
public import FLT.Mazur.IdealCartierNeighborhood

/-!
# From finitely presented ideal stalks to Cartier charts

On an affine open with a finitely presented ideal, a regular generator at a
point spreads to a principal Cartier neighborhood. This uses the actual
scheme stalk localization and the actual restriction of the ideal data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.FCurve
open AnnihilatorSubsheaf
variable {X : Scheme.{u}}

/-- Transport a regular ideal equation between two realizations of a localization. -/
lemma regular_generator_localization_transport {R A B : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (S : Submonoid R) [IsLocalization S A] [IsLocalization S B]
    (I : Ideal R) (a : A) (ha : IsRegular a)
    (hI : I.map (algebraMap R A) = Ideal.span {a}) :
    ∃ b : B, IsRegular b ∧ I.map (algebraMap R B) = Ideal.span {b} := by
  let e := IsLocalization.algEquiv S A B
  refine ⟨e a, ?_, ?_⟩
  · apply isRegular_of_injective_ringHom e.symm.toRingHom e.symm.injective
    simpa using ha
  · have h := congrArg (Ideal.map e.toRingHom) hI
    have he : e.toRingHom.comp (algebraMap R A) = algebraMap R B := by
      ext x
      exact e.commutes x
    rw [Ideal.map_map, he, Ideal.map_span, Set.image_singleton] at h
    exact h

/-- A regular ideal stalk on a finitely presented affine chart extends to a
principal Cartier neighborhood inside that chart. -/
theorem cartierChart_neighborhood_of_stalk (I : X.IdealSheafData) (U : X.affineOpens)
    [Module.FinitePresentation Γ(X, U) (I.ideal U)] (x : X) (hx : x ∈ U.1)
    (hs : ∃ a : X.presheaf.stalk x, IsRegular a ∧ stalkIdeal I x = Ideal.span {a}) :
    ∃ r : Γ(X, U), x ∈ X.basicOpen r ∧ CartierChart I (X.affineBasicOpen r) := by
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  let := U.2.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨a, ha, hIa⟩ := hs
  rw [stalkIdeal_eq_map I x U hx] at hIa
  obtain ⟨r, hr, b, hb, hIb⟩ := ideal_regular_generator_spreads (I.ideal U)
    (U.2.primeIdealOf ⟨x, hx⟩).asIdeal (X.presheaf.stalk x) a ha hIa
  have hxr : x ∈ X.basicOpen r := by
    have hmem : U.2.primeIdealOf ⟨x, hx⟩ ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen r := by
      rw [U.2.fromSpec_preimage_basicOpen]
      exact hr
    change U.2.fromSpec (U.2.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen r at hmem
    simpa only [U.2.fromSpec_primeIdealOf ⟨x, hx⟩] using hmem
  let := U.2.isLocalization_basicOpen r
  obtain ⟨c, hc, hIc⟩ := regular_generator_localization_transport
    (B := Γ(X, X.basicOpen r)) (.powers r) (I.ideal U) b hb hIb
  refine ⟨r, hxr, c, hc, ?_⟩
  rw [← I.map_ideal_basicOpen U r]
  exact hIc

/-- Finite presentation on affine opens and regular principal stalks together
imply the global effective Cartier condition. -/
theorem effectiveCartier_of_finitePresentation_stalks (I : X.IdealSheafData)
    (hfp : ∀ U : X.affineOpens, Module.FinitePresentation Γ(X, U) (I.ideal U))
    (hs : ∀ x : X, ∃ a : X.presheaf.stalk x,
      IsRegular a ∧ stalkIdeal I x = Ideal.span {a}) : EffectiveCartier I := by
  rw [effectiveCartier_iff_basicOpen]
  intro U x hx
  let := hfp U
  exact cartierChart_neighborhood_of_stalk I U x hx (hs x)

end FLT.Mazur.FCurve
