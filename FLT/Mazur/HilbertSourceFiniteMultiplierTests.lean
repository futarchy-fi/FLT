/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceRelationPowerClearing
public import FLT.Mazur.SchemeFiniteSectionAnnihilator

/-!
# Finite tests for original compatible scalar multipliers

Noetherianity of the full original relation selects finitely many raw
invariant numerators. Their compatibility after scalar multiplication tests
compatibility for every raw numerator, even though the original scalar ring
and the raw module over it need not be Noetherian or finite.
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
local instance finiteMultiplierOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance finiteMultiplierOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
variable [IsAffine U.toScheme]


local notation "β" => normalizedBoundaryChartMap f hL d V c k n o U hU


local notation "Δ" => originalSourceRankDiscrepancy f hL d V c k n o U hU
local notation "βsource" => originalSourceCompatibleBoundaryMap f hL d V c k n o W U hU hUW

omit [Etale V.hom] [IsAffine U.toScheme] in
/-- Compatibility of a scalar multiple is annihilation of the full original discrepancy. -/
theorem originalSource_scalar_mul_mem_iff (x : Ω) (a : Sinv) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    σ x * a ∈ Csource ↔
      (F).appTop (σ x).val * ((F).appTop a.val - (H).appTop a.val) = 0 := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  refine (mem_originalSourceCompatibleModule
    f hL d V c k n o W U hU hUW (σ x * a)).trans ?_
  change (F).appTop (σ x * a).val = (H).appTop (σ x * a).val ↔ _
  simp only [Subring.coe_mul, map_mul]
  rw [← normalizedOriginalScalarMap_full_source_relation f hL d V c k n o W U hU hUW x]
  rw [← sub_eq_zero, ← mul_sub]

/-- A finite set of original numerators tests every original scalar multiplier. -/
theorem originalSource_exists_finite_multiplier_tests :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    ∃ S : Finset Sinv, ∀ x : Ω,
      (∀ a ∈ S, σ x * a ∈ Csource) ↔ ∀ a : Sinv, σ x * a ∈ Csource := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := originalSource_doubleRelation_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)
  obtain ⟨S, hS⟩ := SchemeFiniteSectionAnnihilator.exists_finset_annihilator
    (fun a : Sinv ↦ (F).appTop a.val - (H).appTop a.val)
  refine ⟨S, fun x ↦ ?_⟩
  simp_rw [originalSource_scalar_mul_mem_iff]
  exact hS ((F).appTop (σ x).val)

end FLT.Mazur.HilbertChart.AffineRestriction
