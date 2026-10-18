/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarPrincipalNeighborhood
public import FLT.Mazur.SchemeInvariantOpenRelationExtension

/-!
# Constructing original-prime denominators and fixed-target corrections

Avoidance of the closed bad image constructs an original scalar outside the
specified prime. A compatible lift on the stable image domain then yields
an exact boundary-zero correction on the fixed affine target. Every member
of a finite family of full scheme relation equations uses the same scalar.
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
  (FO HO : ∀ a, Z a ⟶ O.toScheme)
  (hF : ∀ a, FO a ≫ O.ι = F a) (hH : ∀ a, HO a ≫ O.ι = H a)
/-- The original scalars as actual target coordinates, retaining their original domain ring. -/
def invariantScalarCoordinates : R →+* Γ(X, ⊤) where
  toFun r := (σ r).val
  map_zero' := congrArg Subtype.val σ.map_zero
  map_one' := congrArg Subtype.val σ.map_one
  map_add' a b := congrArg Subtype.val (σ.map_add a b)
  map_mul' a b := congrArg Subtype.val (σ.map_mul a b)

local notation "σ₀" => invariantScalarCoordinates ρ σ

include hσ hF hH in
/-- Geometric bad-image avoidance constructs both an original denominator and exact correction. -/
theorem originalScalar_open_relation_correction (P : PrimeSpectrum R)
    (hP : P ∈ scalarNeighborhoodLocus σ₀ O)
    (v : invariantCoordinates (restrictedAction ρ O hO)) (u : invariantCoordinates ρ)
    (hb : (i ∣_ O).appTop v.val = (i ⁻¹ᵁ O).ι.appTop (i.appTop u.val))
    (he : ∀ a, (FO a).appTop v.val = (HO a).appTop v.val) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∃ w : invariantCoordinates ρ,
      i.appTop w.val = 0 ∧ ∀ a,
        (F a).appTop w.val - (H a).appTop w.val =
          (F a).appTop (σ r).val * ((F a).appTop u.val - (H a).appTop u.val) := by
  obtain ⟨r, hrP, hr⟩ := (mem_scalarNeighborhoodLocus_iff σ₀ O P).mp hP
  obtain ⟨n, w, hw, hd⟩ := open_principal_relation_correction
    ρ O hO (σ r) hr i F H (fun a ↦ hσ a r) FO HO hF hH v u hb he
  refine ⟨r ^ n, P.asIdeal.primeCompl.pow_mem hrP n, w, hw, ?_⟩
  intro a
  simpa only [map_pow, Subring.coe_pow] using hd a

include hσ hF hH in
/-- The same construction produces a full compatible lift with scaled exact boundary. -/
theorem originalScalar_open_relation_lift (P : PrimeSpectrum R)
    (hP : P ∈ scalarNeighborhoodLocus σ₀ O)
    (v : invariantCoordinates (restrictedAction ρ O hO)) (t : Γ(Y, ⊤))
    (hb : (i ∣_ O).appTop v.val = (i ⁻¹ᵁ O).ι.appTop t)
    (he : ∀ a, (FO a).appTop v.val = (HO a).appTop v.val) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∃ w : invariantCoordinates ρ,
      i.appTop w.val = i.appTop (σ r).val * t ∧
        ∀ a, (F a).appTop w.val = (H a).appTop w.val := by
  obtain ⟨r, hrP, hr⟩ := (mem_scalarNeighborhoodLocus_iff σ₀ O P).mp hP
  obtain ⟨n, w, hw, hd, _⟩ := open_principal_relation_lift_numerator
    ρ O hO (σ r) hr i F H (fun a ↦ hσ a r) FO HO hF hH v t hb he
  refine ⟨r ^ n, P.asIdeal.primeCompl.pow_mem hrP n, w, ?_, hd⟩
  simpa only [map_pow, Subring.coe_pow] using hw

end FLT.Mazur.SchemeFiniteGroupQuotient
