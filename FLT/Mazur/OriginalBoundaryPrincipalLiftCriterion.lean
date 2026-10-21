/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStagePrincipalBoundaryCorrection

/-!
# Constructing principal boundary lifts from original scalar powers

A power in the original lift ideal constructs an actual invariant section on
that original principal open, by dividing its numerator by the restricted
scalar. Together with denominator clearing this identifies the radical of
the original lift ideal exactly, without reversing the rank correction bridge.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections InvariantOpenCoefficientRestriction
open SchemeRelationPrincipalLocalization SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  [CompactSpace D] [QuasiSeparatedSpace D] (r : compatibleFunctions p q)
local notation "U" => A.basicOpen r.val
local notation "hU" => compatibleFunctions_basicOpen p q r

/-- Original invariants restrict to actual full-relation coefficients on their principal open. -/
def originalPrincipalCoefficientMap :
    compatibleFunctions p q →+* coefficients p q U hU :=
  (relationOpenCoordinates p q U hU).toRingHom.comp
    ((openEquiv p q r).toRingHom.comp (algebraMap _ (Localization.Away r)))

/-- The coefficient map is literal restriction of the original function. -/
theorem originalPrincipalCoefficientMap_val (a : compatibleFunctions p q) :
    (originalPrincipalCoefficientMap r a).val = (U).ι.appTop a.val := by
  change (U).topIso.inv ((openEquiv p q r (algebraMap _ (Localization.Away r) a)).val) = _
  rw [openEquiv_algebraMap]
  exact AffineNormGluing.topIso_inv_global (U) a.val

/-- The same original parameter becomes a unit, including in full invariant coefficients. -/
theorem originalPrincipalCoefficientMap_isUnit :
    IsUnit (originalPrincipalCoefficientMap r r) := by
  exact (IsLocalization.Away.algebraMap_isUnit r (S := Localization.Away r)).map
    ((relationOpenCoordinates p q U hU).toRingHom.comp (openEquiv p q r).toRingHom)

attribute [local irreducible] originalPrincipalCoefficientMap

variable (J : A.IdealSheafData) (t : Γ(J.subscheme, ⊤))

private theorem lift_of_unit_power {R B C E : Type*}
    [CommRing R] [CommRing B] [CommRing C] [CommRing E]
    (a : R →+* C) (b : C →+* E) (f : R →+* B) (c : B →+* E)
    (hs : ∀ x, b (a x) = c (f x)) (s : R) (hu : IsUnit (a s))
    (t : B) (N : ℕ) (w : R) (hw : f w = f s ^ N * t) :
    ∃ u : C, b u = c t := by
  obtain ⟨v, hv⟩ := hu
  refine ⟨(↑(v⁻¹) : C) ^ N * a w, ?_⟩
  rw [map_mul, hs, hw, map_mul, map_pow, map_pow, ← hs s, ← hv,
    ← mul_assoc, ← mul_pow, ← map_mul]
  simp only [Units.inv_mul, map_one, one_pow, one_mul]

/-- Divide an exact original numerator to construct a lift on the entire principal relation. -/
theorem exists_principalBoundaryLift_of_pow (N : ℕ)
    (h : r ^ N ∈ originalBoundaryLiftIdeal (p := p) (q := q) J t) :
    ∃ u : coefficients p q U hU, (J.comap (U).ι).subschemeι.appTop u.val =
      (IdealSheafClosedTransitions.map (J.comap (U).ι) J (U).ι rfl).appTop t := by
  obtain ⟨w, hw⟩ := h
  let b : coefficients p q U hU →+* Γ((J.comap (U).ι).subscheme, ⊤) :=
    (J.comap (U).ι).subschemeι.appTop.hom.comp (coefficients p q U hU).subtype
  let c := (IdealSheafClosedTransitions.map (J.comap (U).ι) J (U).ι rfl).appTop.hom
  let f := J.subschemeι.appTop.hom.comp (compatibleFunctions p q).subtype
  have hs (a : compatibleFunctions p q) :
      b (originalPrincipalCoefficientMap r a) = c (f a) := by
    change (J.comap (U).ι).subschemeι.appTop
      (originalPrincipalCoefficientMap r a).val = _
    rw [originalPrincipalCoefficientMap_val]
    exact IdealSheafClosedTransitions.section_square _ _ _ rfl a.val
  apply lift_of_unit_power (originalPrincipalCoefficientMap r) b f c hs r
    (originalPrincipalCoefficientMap_isUnit r) t N w
  change J.subschemeι.appTop w.val = J.subschemeι.appTop r.val ^ N * t
  simpa only [Subring.coe_pow, map_pow] using hw

/-- Radical membership is exactly solvability on that original invariant principal neighborhood. -/
theorem mem_originalBoundaryLiftIdeal_radical_iff_principal :
    r ∈ (originalBoundaryLiftIdeal (p := p) (q := q) J t).radical ↔
      ∃ u : coefficients p q U hU, (J.comap (U).ι).subschemeι.appTop u.val =
        (IdealSheafClosedTransitions.map (J.comap (U).ι) J (U).ι rfl).appTop t := by
  constructor
  · rintro ⟨N, hN⟩
    exact exists_principalBoundaryLift_of_pow r J t N hN
  · rintro ⟨u, hu⟩
    exact exists_pow_mem_originalBoundaryLiftIdeal J t r u hu

end FLT.Mazur.EquivalenceRelationOrderedFrames
