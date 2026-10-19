/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationExactQuotientCorrectionExtension
public import FLT.Mazur.EquivalenceRelationScalarLocalEquations

/-!
# A prescribed finite correction on every complete original scalar fiber

One ambient boundary-zero correction retains the original input and its exact
prescribed stage value. Character containment then makes that same correction
solve the full original relation equations on every qualifying scalar fiber.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
local notation "ρ" => restrictedAction (action e I o) U hU
local notation "hj" => restrictedAction_hom_ι (action e I o) U hU
local notation "α" k => completeQuotientFrameAction e I o U hU k
local notation "j" k => completeQuotientFrameInclusion e I o U hU k
local notation "π" k => pullback.fst (quotientMap ρ) (completeQuotientStageMap e I o U hU k)
local notation "coeff" a:max k:max => completeQuotientCoefficient e I o U hU a k
variable {B : Scheme} (i : B ⟶ source p q I o) [IsClosedImmersion i]
  (τ : Equiv.Perm I →* Aut B)
  (hi : ∀ g, (τ g).hom ≫ i = i ≫ (action e I o g).hom)
local notation "β" => FiniteGroupEquivariantPullback.action ρ τ (action e I o) U.ι i hj hi
local notation "b" => pullback.fst U.ι i
local notation "hb" => FiniteGroupEquivariantPullback.action_fst ρ τ (action e I o) U.ι i hj hi


variable {R : Type} [CommRing R]
  (s : R →+* invariantCoordinates (restrictedAction (action e I o) U hU))
local notation "F" => SchemeRelationRestriction.fst p q (U.ι ≫ first p q I o)
local notation "H" => SchemeRelationRestriction.snd p q (U.ι ≫ first p q I o)
set_option quotPrecheck false
local notation "g" P:max => originalScalarRelationFiberMap e I o U hU s P
local notation "K" P:max => AlgebraicClosure (P : PrimeSpectrum R).asIdeal.ResidueField
local notation "J" => completeAffineOrbitIdeal e I o U hU

/-- A single correction solves the full fibers without any new prime-dependent choices. -/
theorem prescribedCorrection_all_original_scalar_fibers [IsLocallyNoetherian A]
    (hs : s.FiniteType)
    (t : invariantCoordinates β) (a : Γ(U.toScheme, ⊤)) (ha : (b).appTop a = t.val)
    (k : ℕ) (z : Γ(completeQuotientFrame e I o U hU k, ⊤))
    (hz : (pullback.fst (j k) i).appTop z = 0)
    (he : (SourceRestriction.fst (j k) (j k)).appTop z -
        (SourceRestriction.snd (j k) (j k)).appTop z =
      (SourceRestriction.fst (j k) (j k)).appTop (coeff a k) -
        (SourceRestriction.snd (j k) (j k)).appTop (coeff a k)) :
    ∃ z' : Γ(U.toScheme, ⊤), (b).appTop z' = 0 ∧ coeff z' k = z ∧
      ∀ P : PrimeSpectrum R,
        (∀ χ : invariantCoordinates ρ →+* K P, χ.comp s = algebraMap R (K P) →
          J ≤ RingHom.ker χ) →
        (g P ≫ F).appTop z' - (g P ≫ H).appTop z' =
          (g P ≫ F).appTop a - (g P ≫ H).appTop a := by
  obtain ⟨z', hz', he', v', hv'⟩ := completeQuotient_exact_correction_lift
    e I o U hU i τ hi t a ha k z hz he
  refine ⟨z', hz', he', fun P hJ ↦ ?_⟩
  have h := originalScalarRelationFiber_equalizes e I o U hU s P hs hJ v'
  rw [← hv', map_sub, map_sub] at h
  linear_combination -h

/-- Prescribed interpolation also retains every infinitesimal scalar test at once. -/
theorem prescribedCorrection_all_original_scalar_tests [IsLocallyNoetherian A]
    (hs : s.FiniteType)
    (t : invariantCoordinates β) (a : Γ(U.toScheme, ⊤)) (ha : (b).appTop a = t.val)
    (k : ℕ) (z : Γ(completeQuotientFrame e I o U hU k, ⊤))
    (hz : (pullback.fst (j k) i).appTop z = 0)
    (he : (SourceRestriction.fst (j k) (j k)).appTop z -
        (SourceRestriction.snd (j k) (j k)).appTop z =
      (SourceRestriction.fst (j k) (j k)).appTop (coeff a k) -
        (SourceRestriction.snd (j k) (j k)).appTop (coeff a k)) :
    ∃ z' : Γ(U.toScheme, ⊤), (b).appTop z' = 0 ∧ coeff z' k = z ∧
      ∀ P : PrimeSpectrum R,
        (∀ χ : invariantCoordinates ρ →+* K P, χ.comp s = algebraMap R (K P) →
          J ≤ RingHom.ker χ) →
        ∀ (T : Scheme) (u : T ⟶ Spec (.of R)), (∀ x : T, u x = P) →
        let l := scalarTestRelationMap e I o U hU s u
        (l ≫ F).appTop z' - (l ≫ H).appTop z' =
          (l ≫ F).appTop a - (l ≫ H).appTop a := by
  obtain ⟨z', hz', he', v', hv'⟩ := completeQuotient_exact_correction_lift
    e I o U hU i τ hi t a ha k z hz he
  refine ⟨z', hz', he', fun P hJ T u hu ↦ ?_⟩
  have h := scalarTestRelation_equalizes e I o U hU s P hs hJ u hu v'
  rw [← hv', map_sub, map_sub] at h
  dsimp only
  linear_combination -h

/-- Construct a boundary-zero correction without supplying any finite-stage solution. -/
theorem boundaryCorrection_all_original_scalar_tests [IsLocallyNoetherian A]
    (hs : s.FiniteType)
    (t : invariantCoordinates β) (a : Γ(U.toScheme, ⊤)) (ha : (b).appTop a = t.val) :
    ∃ z' : Γ(U.toScheme, ⊤), (b).appTop z' = 0 ∧
      ∀ P : PrimeSpectrum R,
        (∀ χ : invariantCoordinates ρ →+* K P, χ.comp s = algebraMap R (K P) →
          J ≤ RingHom.ker χ) →
        ∀ (T : Scheme) (u : T ⟶ Spec (.of R)), (∀ x : T, u x = P) →
        let l := scalarTestRelationMap e I o U hU s u
        (l ≫ F).appTop z' - (l ≫ H).appTop z' =
          (l ≫ F).appTop a - (l ≫ H).appTop a := by
  obtain ⟨v, hv⟩ := completeBoundary_invariant_surjective e I o U.ι ρ hj i τ hi t
  have hv' : (b).appTop v.val = t.val := congrArg Subtype.val hv
  refine ⟨a - v.val, ?_, fun P hJ T u hu ↦ ?_⟩
  · rw [map_sub, ha, hv', sub_self]
  · have h := scalarTestRelation_equalizes e I o U hU s P hs hJ u hu v
    dsimp only
    rw [map_sub, map_sub, h]
    ring

/-- One correction works on full scalar localizations with complete generizing characters. -/
theorem boundaryCorrection_all_original_scalar_localizations [IsLocallyNoetherian A]
    (hs : s.FiniteType)
    (t : invariantCoordinates β) (a : Γ(U.toScheme, ⊤)) (ha : (b).appTop a = t.val) :
    ∃ z' : Γ(U.toScheme, ⊤), (b).appTop z' = 0 ∧
      ∀ P : PrimeSpectrum R,
        (∀ Q : PrimeSpectrum R, Q.asIdeal ≤ P.asIdeal →
          ∀ χ : invariantCoordinates ρ →+* K Q, χ.comp s = algebraMap R (K Q) →
            J ≤ RingHom.ker χ) →
        let u := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime P.asIdeal)))
        let l := scalarTestRelationMap e I o U hU s u
        (l ≫ F).appTop z' - (l ≫ H).appTop z' =
          (l ≫ F).appTop a - (l ≫ H).appTop a := by
  obtain ⟨v, hv⟩ := completeBoundary_invariant_surjective e I o U.ι ρ hj i τ hi t
  have hv' : (b).appTop v.val = t.val := congrArg Subtype.val hv
  refine ⟨a - v.val, ?_, fun P hJ ↦ ?_⟩
  · rw [map_sub, ha, hv', sub_self]
  · have h := scalarLocalRelation_equalizes e I o U hU s P hs hJ v
    dsimp only at h ⊢
    rw [map_sub, map_sub, h]
    ring

end FLT.Mazur.EquivalenceRelationNormalizedFrames
