/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceUniformScalarDenominators
public import FLT.Mazur.HilbertSourceUniformRelationMultiplier
public import Mathlib.RingTheory.Ideal.Colon

/-!
# The actual ideal of original compatible multipliers

The annihilator of the unchanged raw-to-compatible quotient is computed by
finitely many colon tests. Every member annihilates the entire actual
boundary cokernel. Geometric good-open scalars lie in its radical, but are
not used to define it.
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
local instance actualMultiplierOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance actualMultiplierOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
variable [IsAffine U.toScheme]


local notation "β" => normalizedBoundaryChartMap f hL d V c k n o U hU


local notation "Δ" => originalSourceRankDiscrepancy f hL d V c k n o U hU
local notation "βsource" => originalSourceCompatibleBoundaryMap f hL d V c k n o W U hU hUW

/-- The actual scalar obstruction ideal, defined from the unchanged compatible source. -/
def originalSourceMultiplierIdeal : Ideal Ω := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  exact Module.annihilator Ω (Sinv ⧸ Csource)

local notation "I" => originalSourceMultiplierIdeal f hL d V c k n o W U hU hUW

omit [Etale V.hom] [IsAffine U.toScheme] in
/-- Membership means multiplication takes every raw numerator into the original source. -/
theorem mem_originalSourceMultiplierIdeal (x : Ω) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    x ∈ I ↔ ∀ a : Sinv, σ x * a ∈ Csource := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  change x ∈ Module.annihilator Ω (Sinv ⧸ Csource) ↔ _
  rw [Submodule.annihilator_quotient, Submodule.mem_colon]
  simp only [Set.mem_univ, forall_const]
  rfl

/-- The exact ideal has finitely many original numerator tests without scalar Noetherianity. -/
theorem originalSourceMultiplierIdeal_finite_colon :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    ∃ S : Finset Sinv, I = (Csource).colon (S : Set Sinv) := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  obtain ⟨S, hS⟩ := originalSource_exists_finite_multiplier_tests
    f hL d V c k n o W U hU hUW
  refine ⟨S, ?_⟩
  ext x
  rw [Submodule.mem_colon]
  exact (mem_originalSourceMultiplierIdeal f hL d V c k n o W U hU hUW x).trans
    (hS x).symm

omit [IsAffine U.toScheme] in
/-- Every actual multiplier gives a linear lift of multiplication on the raw source. -/
theorem originalSource_actual_linear_multiplier (x : Ω) (hx : x ∈ I) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    ∃ L : Sinv →ₗ[Ω] Csource,
      (Csource).subtype.comp L = x • LinearMap.id ∧
      (βsource).comp L = x • (α).toLinearMap := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  let L : Sinv →ₗ[Ω] Csource :=
    (x • (LinearMap.id : Sinv →ₗ[Ω] Sinv)).codRestrict Csource
      ((mem_originalSourceMultiplierIdeal f hL d V c k n o W U hU hUW x).mp hx)
  refine ⟨L, ?_, ?_⟩
  · ext a
    rfl
  · ext a
    exact (α).toLinearMap.map_smul x a

/-- The actual ideal annihilates the entire compatible boundary cokernel. -/
theorem originalSourceMultiplierIdeal_le_boundary_annihilator :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    I ≤ Module.annihilator Ω (Bsource ⧸ LinearMap.range βsource) := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  change I ≤ Module.annihilator Ω (Bsource ⧸ LinearMap.range βsource)
  intro x hx
  obtain ⟨L, _, hcomp⟩ := originalSource_actual_linear_multiplier
    f hL d V c k n o W U hU hUW x hx
  rw [Submodule.annihilator_quotient, Submodule.mem_colon]
  intro t _
  obtain ⟨a, rfl⟩ := normalizedBoundaryChartMap_surjective f hL d V c k n o U hU
    (show IsAffine U.toScheme from inferInstance) t
  exact ⟨L a, LinearMap.congr_fun hcomp a⟩

/-- The earlier geometric avoidance ideal lies in the radical of the actual ideal. -/
theorem originalSource_avoidance_le_multiplier_radical :
    SchemeScalarPrincipalNeighborhood.scalarAvoidanceIdeal
      ((F).appTop.hom.comp σ₀) good ≤ (I).radical := by
  intro x hx
  obtain ⟨power, hp⟩ := originalSource_scalar_power_compatible_uniform
    f hL d V c k n o W U hU hUW x
    ((SchemeScalarPrincipalNeighborhood.mem_scalarAvoidanceIdeal_iff _ good x).mp hx)
  exact ⟨power, (mem_originalSourceMultiplierIdeal
    f hL d V c k n o W U hU hUW (x ^ power)).mpr hp⟩

end FLT.Mazur.HilbertChart.AffineRestriction
