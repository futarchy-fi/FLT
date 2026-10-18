/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeStableCoreInvariantSection
public import FLT.Mazur.SchemeStableCoreScalarNeighborhood
public import FLT.Mazur.SchemeOriginalScalarPairOpenLifts
public import FLT.Mazur.SchemeAffineBadComplementLocalIntegral

/-!
# Full original relation lifts from nonstable open sections

Construct the stable open and its invariant section from an ordinary open
section with translate-overlap equations. The original safe prime is
unchanged. Clearing denominators retains the full original relation and
exact boundary value, with no global factorization through the open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open SchemeFiniteOrbitOpenCore SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {G : Type} [Group G] [Finite G]
  {X Y : Scheme} [IsAffine X] [IsAffine Y]
  (ρ : G →* Aut X) (σ : R →+* invariantCoordinates ρ)
  (O : X.Opens) (i : Y ⟶ X)
  {ι : Type} [Finite ι] {Z : ι → Scheme} [∀ a, IsAffine (Z a)]
  (F H : ∀ a, Z a ⟶ X)
  (hσ : ∀ a r, (F a).appTop (σ r).val = (H a).appTop (σ r).val)
local notation "s" => invariantScalarCoordinates ρ σ

include hσ in
/-- An ordinary open lift with overlap equations gives a full original compatible numerator. -/
theorem originalScalar_unstableOpen_relation_lift (P : PrimeSpectrum R)
    (hP : P ∈ scalarNeighborhoodLocus s O)
    (v : Γ(O.toScheme, ⊤))
    (hv : ∀ g : G, (pairOpenFirst O (𝟙 X) (ρ g).hom).appTop v =
      (pairOpenSecond O (𝟙 X) (ρ g).hom).appTop v)
    (t : Γ(Y, ⊤)) (hb : (i ∣_ O).appTop v = (i ⁻¹ᵁ O).ι.appTop t)
    (he : ∀ a, (pairOpenFirst O (F a) (H a)).appTop v =
      (pairOpenSecond O (F a) (H a)).appTop v) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∃ w : invariantCoordinates ρ,
      i.appTop w.val = i.appTop (σ r).val * t ∧
        ∀ a, (F a).appTop w.val = (H a).appTop w.val := by
  let hf := finite_open_orbit ρ O
  apply originalScalar_pairOpen_relation_lift ρ σ (invariantOpen ρ O hf)
    (invariantOpen_stable ρ O hf) i F H hσ P
    (by rwa [scalarNeighborhoodLocus_invariantOpen])
    (invariantCoreSection ρ O hf v hv) t
  · exact invariantCoreSection_boundary ρ O hf v hv i t hb
  · exact fun a ↦ invariantCoreSection_pair ρ O hf v hv (F a) (H a) (he a)

include hσ in
/-- Nonstable local lifts correct an independent invariant lift on the full affine relation. -/
theorem originalScalar_unstableOpen_relation_correction (P : PrimeSpectrum R)
    (hP : P ∈ scalarNeighborhoodLocus s O)
    (v : Γ(O.toScheme, ⊤))
    (hv : ∀ g : G, (pairOpenFirst O (𝟙 X) (ρ g).hom).appTop v =
      (pairOpenSecond O (𝟙 X) (ρ g).hom).appTop v)
    (u : invariantCoordinates ρ)
    (hb : (i ∣_ O).appTop v = (i ⁻¹ᵁ O).ι.appTop (i.appTop u.val))
    (he : ∀ a, (pairOpenFirst O (F a) (H a)).appTop v =
      (pairOpenSecond O (F a) (H a)).appTop v) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∃ w : invariantCoordinates ρ,
      i.appTop w.val = 0 ∧ ∀ a,
        (F a).appTop w.val - (H a).appTop w.val =
          (F a).appTop (σ r).val * ((F a).appTop u.val - (H a).appTop u.val) := by
  let hf := finite_open_orbit ρ O
  apply originalScalar_pairOpen_relation_correction ρ σ (invariantOpen ρ O hf)
    (invariantOpen_stable ρ O hf) i F H hσ P
    (by rwa [scalarNeighborhoodLocus_invariantOpen])
    (invariantCoreSection ρ O hf v hv) u
  · exact invariantCoreSection_boundary ρ O hf v hv i (i.appTop u.val) hb
  · exact fun a ↦ invariantCoreSection_pair ρ O hf v hv (F a) (H a) (he a)

include hσ in
/-- Bad-quotient integrality is checked before taking the core; no new quotient is required. -/
theorem originalScalar_unstableOpen_lift_of_local_badQuotient
    (J : Ideal Γ(X, ⊤))
    (hJ : PrimeSpectrum.zeroLocus (J : Set Γ(X, ⊤)) = X.toSpecΓ '' (O : Set X)ᶜ)
    (P : PrimeSpectrum R)
    (hInt : (OriginalPrimeIntegralFiber.localizedMap
      ((Ideal.Quotient.mk J).comp s) P.asIdeal).IsIntegral)
    (hP : ∀ x : X, scalarMorphism s x = P → x ∈ O)
    (v : Γ(O.toScheme, ⊤))
    (hv : ∀ g : G, (pairOpenFirst O (𝟙 X) (ρ g).hom).appTop v =
      (pairOpenSecond O (𝟙 X) (ρ g).hom).appTop v)
    (t : Γ(Y, ⊤)) (hb : (i ∣_ O).appTop v = (i ⁻¹ᵁ O).ι.appTop t)
    (he : ∀ a, (pairOpenFirst O (F a) (H a)).appTop v =
      (pairOpenSecond O (F a) (H a)).appTop v) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∃ w : invariantCoordinates ρ,
      i.appTop w.val = i.appTop (σ r).val * t ∧
        ∀ a, (F a).appTop w.val = (H a).appTop w.val :=
  originalScalar_unstableOpen_relation_lift ρ σ O i F H hσ P
    (mem_scalarNeighborhoodLocus_of_badQuotient_local_integral s J O hJ P hInt hP)
    v hv t hb he

end FLT.Mazur.SchemeFiniteGroupQuotient
