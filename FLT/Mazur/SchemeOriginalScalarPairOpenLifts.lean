/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOpenPairRelationLifts
public import FLT.Mazur.SchemeOriginalScalarOpenCorrections
public import FLT.Mazur.SchemeAffineBadComplementIntegral

/-!
# Original-prime full relation lifts from local open equations

The original scalar avoidance criterion and a boundary lift compatible on
the common open relation domain construct a full relation-compatible lift
with boundary multiplied by an original scalar outside the specified prime.
Integral bad quotients can supply avoidance without a separately given cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open FiniteGroupRestriction SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {G : Type} [Group G] [Finite G]
  {X Y : Scheme} [IsAffine X] [IsAffine Y]
  (ρ : G →* Aut X) (σ : R →+* invariantCoordinates ρ)
  (O : X.Opens) (hO : ∀ g, (ρ g).hom ⁻¹ᵁ O = O) (i : Y ⟶ X)
  {ι : Type} [Finite ι] {Z : ι → Scheme} [∀ a, IsAffine (Z a)]
  (F H : ∀ a, Z a ⟶ X)
  (hσ : ∀ a r, (F a).appTop (σ r).val = (H a).appTop (σ r).val)
local notation "σ₀" => invariantScalarCoordinates ρ σ

include hσ in
/-- Original-prime denominators construct lifts satisfying all full original relation equations. -/
theorem originalScalar_pairOpen_relation_lift (P : PrimeSpectrum R)
    (hP : P ∈ scalarNeighborhoodLocus σ₀ O)
    (v : invariantCoordinates (restrictedAction ρ O hO)) (t : Γ(Y, ⊤))
    (hb : (i ∣_ O).appTop v.val = (i ⁻¹ᵁ O).ι.appTop t)
    (he : ∀ a, (pairOpenFirst O (F a) (H a)).appTop v.val =
      (pairOpenSecond O (F a) (H a)).appTop v.val) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∃ w : invariantCoordinates ρ,
      i.appTop w.val = i.appTop (σ r).val * t ∧
        ∀ a, (F a).appTop w.val = (H a).appTop w.val := by
  obtain ⟨r, hrP, hr⟩ := (mem_scalarNeighborhoodLocus_iff σ₀ O P).mp hP
  obtain ⟨n, w, hw, hd, _⟩ := pairOpen_principal_relation_lift_numerator
    ρ O hO (σ r) hr i F H (fun a ↦ hσ a r) v t hb he
  refine ⟨r ^ n, P.asIdeal.primeCompl.pow_mem hrP n, w, ?_, hd⟩
  simpa only [map_pow, Subring.coe_pow] using hw

include hσ in
/-- Independent exact lifts receive boundary-zero corrections on the full relation. -/
theorem originalScalar_pairOpen_relation_correction (P : PrimeSpectrum R)
    (hP : P ∈ scalarNeighborhoodLocus σ₀ O)
    (v : invariantCoordinates (restrictedAction ρ O hO)) (u : invariantCoordinates ρ)
    (hb : (i ∣_ O).appTop v.val = (i ⁻¹ᵁ O).ι.appTop (i.appTop u.val))
    (he : ∀ a, (pairOpenFirst O (F a) (H a)).appTop v.val =
      (pairOpenSecond O (F a) (H a)).appTop v.val) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∃ w : invariantCoordinates ρ,
      i.appTop w.val = 0 ∧ ∀ a,
        (F a).appTop w.val - (H a).appTop w.val =
          (F a).appTop (σ r).val * ((F a).appTop u.val - (H a).appTop u.val) := by
  obtain ⟨r, hrP, hr⟩ := (mem_scalarNeighborhoodLocus_iff σ₀ O P).mp hP
  obtain ⟨n, w, hw, hd⟩ := pairOpen_principal_relation_correction
    ρ O hO (σ r) hr i F H (fun a ↦ hσ a r) v u hb he
  refine ⟨r ^ n, P.asIdeal.primeCompl.pow_mem hrP n, w, hw, ?_⟩
  intro a
  simpa only [map_pow, Subring.coe_pow] using hd a

include hσ in
/-- A constructed integral bad complement supplies the original denominator for full lifting. -/
theorem originalScalar_pairOpen_lift_of_badQuotient
    (J : Ideal Γ(X, ⊤))
    (hJ : PrimeSpectrum.zeroLocus (J : Set Γ(X, ⊤)) = X.toSpecΓ '' (O : Set X)ᶜ)
    (hInt : ((Ideal.Quotient.mk J).comp σ₀).IsIntegral) (P : PrimeSpectrum R)
    (hP : ∀ x : X, scalarMorphism σ₀ x = P → x ∈ O)
    (v : invariantCoordinates (restrictedAction ρ O hO)) (t : Γ(Y, ⊤))
    (hb : (i ∣_ O).appTop v.val = (i ⁻¹ᵁ O).ι.appTop t)
    (he : ∀ a, (pairOpenFirst O (F a) (H a)).appTop v.val =
      (pairOpenSecond O (F a) (H a)).appTop v.val) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∃ w : invariantCoordinates ρ,
      i.appTop w.val = i.appTop (σ r).val * t ∧
        ∀ a, (F a).appTop w.val = (H a).appTop w.val :=
  originalScalar_pairOpen_relation_lift ρ σ O hO i F H hσ P
    (mem_scalarNeighborhoodLocus_of_badQuotient_integral σ₀ J O hJ hInt P hP) v t hb he

end FLT.Mazur.SchemeFiniteGroupQuotient
