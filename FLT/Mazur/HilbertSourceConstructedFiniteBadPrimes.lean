/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceConstructedOpenLifts
public import FLT.Mazur.HilbertSourceConstructedRelationNoetherian
public import FLT.Mazur.SchemeScalarFiniteBadPrimes

/-!
# Finite bad-prime obstructions on the actual Hilbert relation

The original proper family supplies Noetherianity of the full relation.
Finitely many actual arrows with incomplete first endpoints detect all
original scalar accumulation. Completeness over all generizations supplies
avoidance without a closed-image or affine bad-quotient hypothesis.
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
local notation "i" => Over.Hom.left (originalBoundarySourceMap f hL d V c k)
local notation "r" => Over.Hom.left (originalClosedFst f hL d V c k)
local notation "s" => Over.Hom.left (originalClosedSnd f hL d V c k)
local notation "z" => Over.Hom.left (originalClosedArrow f hL d V c k)
local notation "hr" => originalClosedFst_isPullback f hL d V c k
local notation "hs" => congrArg Over.Hom.left (originalClosedArrow_snd f hL d V c k)
local notation "m" => originalClosedInvariantMap f hL d V c k
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation AffineRestriction.fst AffineRestriction.snd equivalence
variable (n : ℕ) (o : Fin n)
local notation "N" => normalizedFullRelationFrames f hL d V c k n o
local notation "ρ" => normalizedOriginalBoundaryAction f hL d V c k n o
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
local notation "j" => normalizedOriginalBoundaryInclusion f hL d V c k n o
local notation "b" => normalizedOriginalBoundaryEndpoint f hL d V c k n o
local notation "hj" => normalizedOriginalBoundaryAction_inclusion f hL d V c k n o
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Uc" => (pullOpen ec Wc).val
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
  (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)

local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "Sinv" => invariantCoordinates (restrictedAction τ U hU)
local notation "E" => (pullOpen eo W).val

local notation "kS" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "D" => SchemeRelationRestriction.doubleDomain p q kS
local notation "F" => SchemeRelationRestriction.fst p q kS
local notation "H" => SchemeRelationRestriction.snd p q kS
local notation "τU" => restrictedAction τ U hU
local notation "jU" => j ∣_ U
local notation "σ" => normalizedOriginalScalarMap f hL d V c k n o W U hU hUW
local notation "σ₀" => invariantScalarCoordinates τU σ
local notation "Tsource" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)

attribute [local irreducible] normalizedOriginalScalarMap
  SchemeRelationRestriction.doubleDomain SchemeRelationRestriction.fst
  SchemeRelationRestriction.snd SchemeRelationRestriction.arrow

local notation "Bsource" => invariantCoordinates (boundaryOpenAction ρ τ j hj U hU)
local notation "α" => normalizedOriginalBoundaryHom f hL d V c k n o W U hU hUW

attribute [local irreducible] normalizedOriginalBoundary
  normalizedOriginalBoundaryInclusion normalizedOriginalBoundaryAction
  normalizedFullRelationAction
  originalSourceCompatibleModule

local notation "Csource" => originalSourceCompatibleModule f hL d V c k n o W U hU hUW
local notation "βsource" => originalSourceCompatibleBoundaryMap f hL d V c k n o W U hU hUW

attribute [local irreducible] OriginalPrimeIntegralFiber.localizedMap
  invariantSheaf sourceSheaf invariantInclusion originalClosedSectionPullback
  invariantScalarCoordinates

open SchemeScalarPrincipalNeighborhood
local notation "Lgood" => originalSourceGoodRelationOpen f hL d V c k n o U hU
local notation "Ogood" => originalSourceConstructedOpen f hL d V c k n o U hU
local notation "σR" => (F).appTop.hom.comp σ₀


/-- Every bad original arrow has an incomplete first endpoint. -/
theorem originalSource_badRelation_first_incomplete (x : D)
    (hx : x ∉ Lgood) :
    (F ≫ U.ι) x ∉ completePointLocus («p» := p) («q» := q) (Fin n) o :=
  fun hc ↦ hx (originalSourceGoodRelationOpen_contains f hL d V c k n o U hU hc)

/-- The actual source chart has a finite, coefficient-independent list of bad-prime tests. -/
theorem originalSource_exists_finite_badPrime_tests (ha : IsAffineOpen U) :
    ∃ Ebad : Set D, Ebad.Finite ∧ Ebad ⊆ (Lgood : Set D)ᶜ ∧
      (∀ x ∈ Ebad,
        (F ≫ U.ι) x ∉ completePointLocus («p» := p) («q» := q) (Fin n) o) ∧
      ∀ P : Ideal Tsource, ∀ hP : P.IsPrime,
        PrimeSpectrum.comap κ ⟨P, hP⟩ ∈ scalarNeighborhoodLocus σR Lgood ↔
          ∀ x ∈ Ebad, ¬ (scalarMorphism σR x).asIdeal ≤ P.comap κ := by
  let _ := originalSource_doubleRelation_isNoetherian f hL d V c k n o U ha
  obtain ⟨Ebad, hfin, hbad, htest⟩ := exists_finite_scalar_bad_primes σR Lgood
  exact ⟨Ebad, hfin, hbad,
    fun x hx ↦ originalSource_badRelation_first_incomplete f hL d V c k n o U hU x (hbad hx),
    fun P hP ↦ htest (PrimeSpectrum.comap κ ⟨P, hP⟩)⟩

/-- Completeness above all original generizations controls the entire bad-image closure. -/
theorem originalSourceConstructedOpen_safe_of_complete_generizations (ha : IsAffineOpen U)
    (P : Ideal Tsource) [P.IsPrime]
    (hP : ∀ x : U.toScheme, (scalarMorphism σ₀ x).asIdeal ≤ P.comap κ →
      U.ι x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    PrimeSpectrum.comap κ ⟨P, inferInstance⟩ ∈ scalarNeighborhoodLocus σR Lgood := by
  let _ := originalSource_doubleRelation_isNoetherian f hL d V c k n o U ha
  apply (mem_scalarNeighborhoodLocus_iff_generizations
    σR Lgood (PrimeSpectrum.comap κ ⟨P, inferInstance⟩)).mpr
  intro x hx
  apply originalSourceGoodRelationOpen_contains f hL d V c k n o U hU
  apply hP (F x)
  rw [scalarMorphism_comp] at hx
  exact hx

end FLT.Mazur.HilbertChart.AffineRestriction
