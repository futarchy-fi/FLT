/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceActualMultiplierIdeal
public import Mathlib.RingTheory.Support

/-!
# Closed support of the actual original compatibility quotient

Finite discrepancy tests make the support closed even without finiteness
over the original scalar ring. A point of this support has one persistent
original numerator obstructing every denominator, at bounded higher ranks.
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
local notation "boundaryOrbitMap" => originalClosedInvariantMap f hL d V c k
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
local notation "Wc" => (TopologicalSpace.Opens.map (boundaryOrbitMap).base).obj W
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


open RelativeOrderedTuples
attribute [local irreducible] originalSourceCompatibleModule
local notation "endpoint" => F ≫ kS
local notation "cutoff" => originalFrameRankCutoff f hL d V c k
local notation "good" => originalSourceGoodRelationOpen f hL d V c k n o U hU
local notation "Csource" => originalSourceCompatibleModule f hL d V c k n o W U hU hUW
local instance multiplierSupportOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance multiplierSupportOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
variable [IsAffine U.toScheme]


local notation "β" => normalizedBoundaryChartMap f hL d V c k n o U hU


local notation "Δ" => originalSourceRankDiscrepancy f hL d V c k n o U hU
local notation "βsource" => originalSourceCompatibleBoundaryMap f hL d V c k n o W U hU hUW

local notation "I" => originalSourceMultiplierIdeal f hL d V c k n o W U hU hUW

/-- Local vanishing of the entire compatibility quotient constructs one original multiplier. -/
theorem originalSource_not_support_iff_multiplier (P : PrimeSpectrum Ω) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    P ∉ Module.support Ω (Sinv ⧸ Csource) ↔ ∃ x : P.asIdeal.primeCompl, x.val ∈ I := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  change P ∉ Module.support Ω (Sinv ⧸ Csource) ↔ ∃ x : P.asIdeal.primeCompl, x.val ∈ I
  rw [Module.notMem_support_iff']
  constructor
  · intro h
    have hpoint (a : Sinv) : ∃ x : P.asIdeal.primeCompl, σ x.val * a ∈ Csource := by
      obtain ⟨x, hx, hz⟩ := h (Submodule.Quotient.mk a)
      refine ⟨⟨x, hx⟩, ?_⟩
      change Submodule.Quotient.mk (σ x * a) = 0 at hz
      exact (Submodule.Quotient.mk_eq_zero Csource).mp hz
    obtain ⟨x, hx⟩ := (originalSource_uniform_denominator_iff
      f hL d V c k n o W U hU hUW P.asIdeal.primeCompl).mp hpoint
    exact ⟨x, (mem_originalSourceMultiplierIdeal
      f hL d V c k n o W U hU hUW x.val).mpr hx⟩
  · rintro ⟨x, hx⟩ qv
    induction qv using Submodule.Quotient.induction_on with
    | _ a =>
      refine ⟨x.val, x.property, ?_⟩
      change Submodule.Quotient.mk (σ x.val * a) = 0
      exact (Submodule.Quotient.mk_eq_zero Csource).mpr
        ((mem_originalSourceMultiplierIdeal f hL d V c k n o W U hU hUW x.val).mp hx a)

/-- The actual quotient has closed scalar support without assuming it finite over scalars. -/
theorem originalSource_compatibility_support_eq_zeroLocus :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    Module.support Ω (Sinv ⧸ Csource) = PrimeSpectrum.zeroLocus (I : Set Ω) := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  change Module.support Ω (Sinv ⧸ Csource) = PrimeSpectrum.zeroLocus (I : Set Ω)
  ext P
  have he : P ∉ Module.support Ω (Sinv ⧸ Csource) ↔
      ∃ x : P.asIdeal.primeCompl, x.val ∈ I :=
    originalSource_not_support_iff_multiplier f hL d V c k n o W U hU hUW P
  rw [← not_iff_not, he]
  change (∃ x : P.asIdeal.primeCompl, x.val ∈ I) ↔ ¬ I ≤ P.asIdeal
  constructor
  · rintro ⟨x, hx⟩ h
    exact x.property (h hx)
  · intro h
    obtain ⟨x, hx, hp⟩ := IsConcreteLE.not_le_iff_exists.mp h
    exact ⟨⟨x, hp⟩, hx⟩

/-- Every boundary obstruction lies in the closed support of the original compatibility quotient. -/
theorem originalSource_boundary_support_subset_compatibility :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Module.support Ω (Bsource ⧸ LinearMap.range βsource) ⊆
      Module.support Ω (Sinv ⧸ Csource) := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  change Module.support Ω (Bsource ⧸ LinearMap.range βsource) ⊆
    Module.support Ω (Sinv ⧸ Csource)
  have he : Module.support Ω (Sinv ⧸ Csource) = PrimeSpectrum.zeroLocus (I : Set Ω) :=
    originalSource_compatibility_support_eq_zeroLocus f hL d V c k n o W U hU hUW
  rw [he]
  intro P hP
  exact (originalSourceMultiplierIdeal_le_boundary_annihilator
    f hL d V c k n o W U hU hUW).trans (Module.annihilator_le_of_mem_support hP)

/-- A finite original numerator list witnesses every persistent higher-rank scalar obstruction. -/
theorem originalSource_finite_persistent_rank_witnesses :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    ∃ S : Finset Sinv, ∀ P : PrimeSpectrum Ω,
      P ∈ Module.support Ω (Sinv ⧸ Csource) ↔
        ∃ a ∈ S, ∀ x : P.asIdeal.primeCompl, ∃ m : ℕ,
          n < m ∧ m ≤ cutoff ∧ ∃ order : ℕ, Δ m order (σ x.val * a) ≠ 0 := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  obtain ⟨S, hS⟩ := originalSource_finite_uniform_higher_rank_tests
    f hL d V c k n o W U hU hUW
  refine ⟨S, fun P ↦ ?_⟩
  have he : P ∉ Module.support Ω (Sinv ⧸ Csource) ↔
      ∀ a ∈ S, ∃ x : P.asIdeal.primeCompl,
        ∀ m : ℕ, n < m → m ≤ cutoff → ∀ order : ℕ, Δ m order (σ x.val * a) = 0 := by
    refine (originalSource_not_support_iff_multiplier
      f hL d V c k n o W U hU hUW P).trans ?_
    refine (exists_congr (fun x : P.asIdeal.primeCompl ↦ ?_)).trans
      (hS P.asIdeal.primeCompl).symm
    exact mem_originalSourceMultiplierIdeal f hL d V c k n o W U hU hUW x.val
  have h := not_congr he
  push Not at h
  exact h

end FLT.Mazur.HilbertChart.AffineRestriction
