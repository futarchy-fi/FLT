/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceConstructedBadPrimeLifts
public import FLT.Mazur.SchemeScalarBoundaryUnitCover

/-!
# A finite equation for universal original Hilbert boundary avoidance

The exact denominator ideal lives in the unchanged invariant scalar ring.
Its image in the original boundary section ring is the unit ideal exactly
when every original boundary prime is safe. A finite unit equation then
supplies full localized source surjectivity at all of those primes.
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


/-- Universal original boundary safety is equivalent to a concrete unit-ideal condition. -/
theorem originalSource_all_primes_safe_iff :
    (∀ P : PrimeSpectrum Tsource,
      PrimeSpectrum.comap κ P ∈ scalarNeighborhoodLocus σR Lgood) ↔
      Ideal.map κ (SchemeOpenEnvelope.denominatorIdeal σR Lgood) = ⊤ :=
  scalar_boundary_cover_iff_unit_ideal σR Lgood κ

/-- Universal safety admits a finite equation in the unchanged original boundary section ring. -/
theorem originalSource_all_primes_safe_iff_finite_equation :
    (∀ P : PrimeSpectrum Tsource,
      PrimeSpectrum.comap κ P ∈ scalarNeighborhoodLocus σR Lgood) ↔
      ∃ (m' : ℕ) (a : Fin m' → Ω) (weights : Fin m' → Tsource),
        (∀ idx, (D).basicOpen (σR (a idx)) ≤ Lgood) ∧
          ∑ idx, weights idx * κ (a idx) = 1 :=
  (originalSource_all_primes_safe_iff f hL d V c k n o W U hU hUW).trans
    (scalar_boundary_unit_ideal_iff_finite_equation σR Lgood κ)

/-- A finite original boundary unit equation supplies every required safe prime. -/
theorem originalSource_all_primes_safe_of_unit_sum {I : Type} [Fintype I]
    (a : I → Ω) (weights : I → Tsource)
    (ha : ∀ idx, (D).basicOpen (σR (a idx)) ≤ Lgood)
    (hab : ∑ idx, weights idx * κ (a idx) = 1) :
    ∀ P : PrimeSpectrum Tsource,
      PrimeSpectrum.comap κ P ∈ scalarNeighborhoodLocus σR Lgood :=
  scalar_boundary_cover_of_unit_sum σR Lgood κ a weights ha hab

/-- The finite unit certificate yields full source surjectivity at every original boundary prime. -/
theorem originalSource_all_primes_surjective_of_unit_sum (ha : IsAffineOpen U)
    {I : Type} [Fintype I] (a : I → Ω) (weights : I → Tsource)
    (haO : ∀ idx, (D).basicOpen (σR (a idx)) ≤ Lgood)
    (hab : ∑ idx, weights idx * κ (a idx) = 1) (P : Ideal Tsource) [P.IsPrime] :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Function.Surjective
      (originalSourceLocalizedCompatibleBoundaryMap f hL d V c k n o W U hU hUW P) :=
  originalSource_constructedOpen_surjective f hL d V c k n o W U hU hUW ha P
    (originalSource_all_primes_safe_of_unit_sum f hL d V c k n o W U hU hUW
      a weights haO hab ⟨P, inferInstance⟩)

end FLT.Mazur.HilbertChart.AffineRestriction
