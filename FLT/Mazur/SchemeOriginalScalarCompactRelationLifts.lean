/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOriginalScalarPairOpenLifts
public import FLT.Mazur.SchemeOpenPairBaseRestriction

/-!
# Full original relation lifting on quasicompact relation schemes

Choose a finite affine cover of the actual relation, clear all its equations
with one original scalar, and use scheme descent to detect the full equation.
The relation and its common usable open need not be affine. Residual points
and nilpotents are included in the resulting equation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open FiniteGroupRestriction SchemeScalarPrincipalNeighborhood SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- An actual scheme open cover detects equality of full regular functions. -/
theorem pairOpen_cover_sections_ext {Z : Scheme} (C : Z.OpenCover)
    {s t : Γ(Z, ⊤)} (h : ∀ a, (C.f a).appTop s = (C.f a).appTop t) : s = t := by
  apply (functionEquiv Z).symm.injective
  apply C.hom_ext
  intro a
  apply (functionEquiv (C.X a)).injective
  simpa only [functionEquiv_comp, Equiv.apply_symm_apply] using h a

variable {R : Type} [CommRing R] {G : Type} [Group G] [Finite G]
  {X Y Z : Scheme} [IsAffine X] [IsAffine Y] [CompactSpace Z]
  (ρ : G →* Aut X) (σ : R →+* invariantCoordinates ρ)
  (O : X.Opens) (hO : ∀ g, (ρ g).hom ⁻¹ᵁ O = O) (i : Y ⟶ X)
  (F H : Z ⟶ X) (hσ : ∀ r, F.appTop (σ r).val = H.appTop (σ r).val)
local notation "σ₀" => invariantScalarCoordinates ρ σ

include hσ in
/-- A finite affine relation cover constructs a full compatible original-prime numerator. -/
theorem originalScalar_compact_relation_lift (P : PrimeSpectrum R)
    (hP : P ∈ scalarNeighborhoodLocus σ₀ O)
    (v : invariantCoordinates (restrictedAction ρ O hO)) (t : Γ(Y, ⊤))
    (hb : (i ∣_ O).appTop v.val = (i ⁻¹ᵁ O).ι.appTop t)
    (he : (pairOpenFirst O F H).appTop v.val = (pairOpenSecond O F H).appTop v.val) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∃ w : invariantCoordinates ρ,
      i.appTop w.val = i.appTop (σ r).val * t ∧ F.appTop w.val = H.appTop w.val := by
  let C := Z.affineCover.finiteSubcover
  obtain ⟨r, hr, w, hb', he'⟩ := originalScalar_pairOpen_relation_lift ρ σ O hO i
    (fun a ↦ C.f a ≫ F) (fun a ↦ C.f a ≫ H)
    (fun a r ↦ congrArg (fun t ↦ (C.f a).appTop t) (hσ r)) P hP v t hb
    (fun a ↦ pairOpen_equation_base O F H (C.f a) v.val he)
  refine ⟨r, hr, w, hb', pairOpen_cover_sections_ext C ?_⟩
  intro a
  exact he' a

include hσ in
/-- The same numerator gives exact boundary-zero corrections on the entire nonaffine relation. -/
theorem originalScalar_compact_relation_correction (P : PrimeSpectrum R)
    (hP : P ∈ scalarNeighborhoodLocus σ₀ O)
    (v : invariantCoordinates (restrictedAction ρ O hO)) (u : invariantCoordinates ρ)
    (hb : (i ∣_ O).appTop v.val = (i ⁻¹ᵁ O).ι.appTop (i.appTop u.val))
    (he : (pairOpenFirst O F H).appTop v.val = (pairOpenSecond O F H).appTop v.val) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∃ w : invariantCoordinates ρ,
      i.appTop w.val = 0 ∧ F.appTop w.val - H.appTop w.val =
        F.appTop (σ r).val * (F.appTop u.val - H.appTop u.val) := by
  obtain ⟨r, hr, w, hw, he'⟩ := originalScalar_compact_relation_lift
    ρ σ O hO i F H hσ P hP v (i.appTop u.val) hb he
  refine ⟨r, hr, σ r * u - w, ?_, ?_⟩
  · change i.appTop ((σ r).val * u.val - w.val) = 0
    simp only [map_sub, map_mul, hw, sub_self]
  · change F.appTop ((σ r).val * u.val - w.val) -
      H.appTop ((σ r).val * u.val - w.val) = _
    simp only [map_sub, map_mul, ← hσ r, he']
    ring

end FLT.Mazur.SchemeFiniteGroupQuotient
