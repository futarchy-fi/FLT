/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceFiniteMultiplierTests
public import FLT.Mazur.FiniteBaseLocalizationDenominators

/-!
# One original scalar from finitely many exact numerator equations

Finite discrepancy tests combine individual scalar denominators into a
single multiplier for every raw numerator. Each individual test must still
solve all bounded higher ranks and all orders with its one denominator.
No good-open containment or finite generation over the scalar ring is assumed.
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
local instance uniformDenominatorOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance uniformDenominatorOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
variable [IsAffine U.toScheme]


local notation "β" => normalizedBoundaryChartMap f hL d V c k n o U hU


local notation "Δ" => originalSourceRankDiscrepancy f hL d V c k n o U hU
local notation "βsource" => originalSourceCompatibleBoundaryMap f hL d V c k n o W U hU hUW

/-- One finite list tests existence of a common multiplier in any original multiplicative set. -/
theorem originalSource_finite_uniform_denominator_tests :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    ∃ S : Finset Sinv, ∀ M : Submonoid Ω,
      (∀ a ∈ S, ∃ x : M, σ x.val * a ∈ Csource) ↔
        ∃ x : M, ∀ a : Sinv, σ x.val * a ∈ Csource := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  obtain ⟨S, hS⟩ := originalSource_exists_finite_multiplier_tests
    f hL d V c k n o W U hU hUW
  refine ⟨S, fun M ↦ ⟨fun h ↦ ?_, fun ⟨x, hx⟩ a _ ↦ ⟨x, hx a⟩⟩⟩
  choose x hx using fun a : S ↦ h a.val a.property
  obtain ⟨y, hy⟩ := FiniteBaseLocalizationDenominators.exists_common_multiple M x
  refine ⟨y, (hS y.val).mp ?_⟩
  intro a ha
  obtain ⟨u, hu⟩ := hy ⟨a, ha⟩
  rw [hu, Submonoid.coe_mul, map_mul, mul_assoc]
  exact (Csource).smul_mem u.val (hx ⟨a, ha⟩)

/-- Pointwise original denominators give one denominator for the entire compatible source. -/
theorem originalSource_uniform_denominator_iff (M : Submonoid Ω) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    (∀ a : Sinv, ∃ x : M, σ x.val * a ∈ Csource) ↔
      ∃ x : M, ∀ a : Sinv, σ x.val * a ∈ Csource := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  obtain ⟨S, hS⟩ := originalSource_finite_uniform_denominator_tests
    f hL d V c k n o W U hU hUW
  exact ⟨fun h ↦ (hS M).mp (fun a _ ↦ h a), fun ⟨x, hx⟩ a ↦ ⟨x, hx a⟩⟩

/-- Finite numerator tests require simultaneous higher-rank equations, not orderwise solutions. -/
theorem originalSource_finite_uniform_higher_rank_tests :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    ∃ S : Finset Sinv, ∀ M : Submonoid Ω,
      (∀ a ∈ S, ∃ x : M, ∀ m : ℕ, n < m → m ≤ cutoff → ∀ order : ℕ,
        Δ m order (σ x.val * a) = 0) ↔
      ∃ x : M, ∀ a : Sinv, σ x.val * a ∈ Csource := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  obtain ⟨S, hS⟩ := originalSource_finite_uniform_denominator_tests
    f hL d V c k n o W U hU hUW
  refine ⟨S, fun M ↦ ?_⟩
  rw [← hS M]
  apply forall_congr'
  intro a
  apply forall_congr'
  intro _
  apply exists_congr
  intro x
  simpa only [originalSourceRankDiscrepancy_eq_zero] using
    (originalSource_mem_iff_higher_rank_equations
      f hL d V c k n o W U hU hUW (σ x.val * a)).symm

end FLT.Mazur.HilbertChart.AffineRestriction
