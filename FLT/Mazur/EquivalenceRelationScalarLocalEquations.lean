/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationScalarSupportedBaseChange

/-!
# Exact equations over the full original scalar localization

Character containment at every generization of the original scalar prime
controls the full localization, not just its closed fiber. The localization
retains all nilpotents. No local-integrality hypothesis is added.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient ScalarTestLocalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
local notation "k" => U.ι ≫ first p q I o
local notation "F" => SchemeRelationRestriction.fst p q k
local notation "H" => SchemeRelationRestriction.snd p q k
local notation "Rel" => SchemeRelationRestriction.doubleDomain p q k
local notation "ρ" => restrictedAction (action e I o) U hU
local notation "J" => completeAffineOrbitIdeal e I o U hU
variable {R : Type} [CommRing R]
  (s : R →+* invariantCoordinates (restrictedAction (action e I o) U hU))
  (P : PrimeSpectrum R)
local notation "K" => AlgebraicClosure P.asIdeal.ResidueField
local notation "φ" => F ≫ quotientMap ρ ≫ Spec.map (CommRingCat.ofHom s)

/-- Full character containment over a set of scalar primes controls every scheme test there. -/
theorem scalarTestRelation_equalizes_over_primes [IsLocallyNoetherian A]
    (hs : s.FiniteType) (Z : Set (PrimeSpectrum R))
    (hJ : ∀ Q ∈ Z, ∀ χ : invariantCoordinates ρ →+*
      AlgebraicClosure Q.asIdeal.ResidueField,
      χ.comp s = algebraMap R _ → J ≤ RingHom.ker χ)
    {T : Scheme} (b : T ⟶ Spec (.of R)) (hb : ∀ x : T, b x ∈ Z)
    (t : invariantCoordinates ρ) :
    (scalarTestRelationMap e I o U hU s b ≫ F).appTop t.val =
      (scalarTestRelationMap e I o U hU s b ≫ H).appTop t.val := by
  apply completeOrbitSupportedTest_equalizes e I o U hU _ _ t
  rw [← completeAffineOrbitIdeal_zeroLocus]
  rintro _ ⟨x, rfl⟩ a ha
  have hc := congrArg (fun f ↦ f x) (pullback.condition (f := φ) (g := b))
  change PrimeSpectrum.comap s
    ((scalarTestRelationMap e I o U hU s b ≫ F ≫ quotientMap ρ) x) =
      b (pullback.snd φ b x) at hc
  apply (residueGeometricTest_iff_original_fiber s _ hs a).mp _ _ hc
  exact (residueGeometricTest_iff s _ a).mpr
    (fun χ hχ ↦ hJ _ (hb _) χ hχ ha)

omit [Etale p] [IsAffine U.toScheme] in
/-- Every point of the unreduced scalar localization contracts below the original prime. -/
theorem scalarLocalization_center_le
    (x : PrimeSpectrum (Localization.AtPrime P.asIdeal)) :
    (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime P.asIdeal)) x).asIdeal ≤
      P.asIdeal := by
  intro r hr
  by_contra hn
  exact x.asIdeal.notMem_of_isUnit
    (IsLocalization.map_units (M := P.asIdeal.primeCompl)
      (Localization.AtPrime P.asIdeal) ⟨r, hn⟩) hr

/-- Generizing character containment gives exact equations on the full original localization. -/
theorem scalarLocalRelation_equalizes [IsLocallyNoetherian A] (hs : s.FiniteType)
    (hJ : ∀ Q : PrimeSpectrum R, Q.asIdeal ≤ P.asIdeal →
      ∀ χ : invariantCoordinates ρ →+* AlgebraicClosure Q.asIdeal.ResidueField,
        χ.comp s = algebraMap R _ → J ≤ RingHom.ker χ) (t : invariantCoordinates ρ) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime P.asIdeal)))
    (scalarTestRelationMap e I o U hU s b ≫ F).appTop t.val =
      (scalarTestRelationMap e I o U hU s b ≫ H).appTop t.val := by
  apply scalarTestRelation_equalizes_over_primes e I o U hU s hs
    {Q | Q.asIdeal ≤ P.asIdeal} hJ _ _ t
  exact scalarLocalization_center_le P

end FLT.Mazur.EquivalenceRelationNormalizedFrames
