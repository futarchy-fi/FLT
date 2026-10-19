/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceInvariantCharacterOrbits
public import FLT.Mazur.EquivalenceRelationMinimalScalarGeometry
public import FLT.Mazur.AffineBoundaryMinimalScalarGeometry

/-!
# Original Hilbert neighborhoods from complete generic scalar branches

Flatness is imposed on the original source scalar coordinates. Complete lifts
of generic invariant characters then construct full original boundary scalar
neighborhoods, exact test-chart equations and a matching rank stage. The frame
size n is preserved. Flatness and the generic lifts remain to be established.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
local notation "eo" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation AffineRestriction.fst AffineRestriction.snd equivalence
variable (n : ℕ) (o : Fin n)
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
  (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)

local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "Sinv" => invariantCoordinates (restrictedAction τ U hU)

local notation "τU" => restrictedAction τ U hU
local notation "σ" => normalizedOriginalScalarMap f hL d V c k n o W U hU hUW
local notation "σ₀" => invariantScalarCoordinates τU σ
local notation "Tsource" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)

attribute [local irreducible] normalizedOriginalScalarMap
  SchemeRelationRestriction.doubleDomain SchemeRelationRestriction.fst
  SchemeRelationRestriction.snd SchemeRelationRestriction.arrow

attribute [local irreducible] normalizedOriginalBoundary
  normalizedOriginalBoundaryInclusion normalizedOriginalBoundaryAction
  originalSourceCompatibleModule

attribute [local irreducible] OriginalPrimeIntegralFiber.localizedMap
  invariantSheaf sourceSheaf invariantInclusion originalClosedSectionPullback
  invariantScalarCoordinates

open SchemeScalarPrincipalNeighborhood

variable [IsAffine U.toScheme]
local instance minimalCharacterChartNoetherian : IsNoetherian U.toScheme :=
  originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

open AffineScalarBoundaryNilpotence RelativeOrderedTuples
attribute [local irreducible] boundaryProduct boundaryCoordinate
local instance minimalCharacterOver_etale : Etale (Over.mk p).hom :=
  inferInstanceAs (Etale p)
local instance minimalCharacterOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local notation "rankOf" => boundaryPointRank n o U e hU σ κ

local instance minimalCharacterProjection_quasiFinite : LocallyQuasiFinite p :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)

open ScalarTestLocalization
attribute [local irreducible] boundaryPointRank boundaryScalarProjection

local notation "K" P => AlgebraicClosure (PrimeSpectrum.comap κ P).asIdeal.ResidueField
local notation "u" w => sourceCharacterMap (X := U.toScheme) w ≫ U.ι

local notation "J" => completeAffineOrbitIdeal e (Fin n) o U hU

local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU

/-- Complete generic lifts and source flatness construct the full original scalar neighborhood. -/
theorem originalSource_nilpotence_of_minimal_complete_lifts (P : PrimeSpectrum Tsource)
    (hf : (invariantScalarCoordinates τU σ).Flat)
    (hc : ∀ Q : PrimeSpectrum Ω, Q.asIdeal ∈ minimalPrimes Ω →
      Q ≤ PrimeSpectrum.comap κ P →
      ∀ χ : Sinv →+* AlgebraicClosure Q.asIdeal.ResidueField,
        χ.comp σ = algebraMap Ω _ →
        ∃ w : Γ(U.toScheme, ⊤) →+* AlgebraicClosure Q.asIdeal.ResidueField,
          (∀ t : Sinv, w t.val = χ t) ∧ Complete (Fin n) o (u w)) :
    P ∈ boundaryScalarNilpotenceOpen σ κ tests := by
  apply boundaryScalar_mem_of_minimal_characters σ κ tests P
    (originalSource_invariantScalar_finiteType f hL d V c k n o W U hU hUW)
    (invariantScalar_generalizing_of_source_flat τU σ hf)
  intro Q hQ hQP χ hχ t ht
  obtain ⟨w, hw, hwc⟩ := hc Q hQ hQP χ hχ
  exact (hw t).symm.trans (complete_character_tests_vanish e (Fin n) o U hU w hwc t ht)

attribute [local irreducible] boundaryPrincipalProjection boundaryPrincipalEndpoint
  boundaryScalarHom

/-- The constructed neighborhood recovers a finite thickened stage with the original n. -/
theorem originalSource_rank_chart_of_minimal_complete_lifts (P : PrimeSpectrum Tsource)
    (hf : (invariantScalarCoordinates τU σ).Flat)
    (hc : ∀ Q : PrimeSpectrum Ω, Q.asIdeal ∈ minimalPrimes Ω →
      Q ≤ PrimeSpectrum.comap κ P →
      ∀ χ : Sinv →+* AlgebraicClosure Q.asIdeal.ResidueField,
        χ.comp σ = algebraMap Ω _ →
        ∃ w : Γ(U.toScheme, ⊤) →+* AlgebraicClosure Q.asIdeal.ResidueField,
          (∀ t : Sinv, w t.val = χ t) ∧ Complete (Fin n) o (u w)) :
    ∃ r : Tsource, r ∉ P.asIdeal ∧ ∃ stage : ℕ,
      IsIso (rankPullbackMap (Over.mk p)
        (boundaryPrincipalEndpoint n o U e hU σ κ (boundaryScalarHom σ κ r)) n stage) := by
  apply originalSource_scalar_rank_chart f hL d V c k n o W U hU hUW P
  exact originalSource_nilpotence_of_minimal_complete_lifts
    f hL d V c k n o W U hU hUW P hf hc

end FLT.Mazur.HilbertChart.AffineRestriction
