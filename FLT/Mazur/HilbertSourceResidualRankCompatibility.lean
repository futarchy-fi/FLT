/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceCompatibleModule
public import FLT.Mazur.HilbertSourceRelationRankStages
public import FLT.Mazur.HilbertSourceConstructedRelationNoetherian

/-!
# Higher-rank detection of the unchanged compatible source module

The original full relation is Noetherian by the Hilbert hypotheses. All its
matching-rank equations are already solved for every invariant numerator.
Membership in the original scalar module is therefore exactly the remaining
bounded higher-rank equations, with every order and every nilpotent retained.
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
local instance residualModuleOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance residualModuleOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
variable [IsAffine U.toScheme]

/-- Full original compatibility is detected solely by the bounded higher-rank equations. -/
theorem originalSource_mem_iff_higher_rank_equations (a : Sinv) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    a ∈ Csource ↔ ∀ m : ℕ, n < m → m ≤ cutoff → ∀ order : ℕ,
      (rankPullbackMap (Over.mk p) endpoint m order ≫ F).appTop a.val =
        (rankPullbackMap (Over.mk p) endpoint m order ≫ H).appTop a.val := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  let _ := originalSource_doubleRelation_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)
  refine (mem_originalSourceCompatibleModule f hL d V c k n o W U hU hUW a).trans ?_
  change (F).appTop a.val = (H).appTop a.val ↔ _
  exact section_eq_iff_higher_rank_stages (Over.mk p) endpoint n good cutoff
    (originalSource_relation_rank_interval f hL d V c k n o U)
    (originalSource_relation_matching_good f hL d V c k n o U hU)
    ((F).appTop a.val) ((H).appTop a.val)
    (originalSourceGoodRelationOpen_equalizes f hL d V c k n o U hU a)

/-- Nonmembership has an actual finite-order higher-rank discrepancy in the original relation. -/
theorem originalSource_not_mem_higher_rank_witness (a : Sinv)
    (ha : let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
      a ∉ Csource) :
    ∃ m : ℕ, n < m ∧ m ≤ cutoff ∧ ∃ order : ℕ,
      (rankPullbackMap (Over.mk p) endpoint m order ≫ F).appTop a.val ≠
        (rankPullbackMap (Over.mk p) endpoint m order ≫ H).appTop a.val := by
  by_contra h
  push Not at h
  exact ha ((originalSource_mem_iff_higher_rank_equations
    f hL d V c k n o W U hU hUW a).mpr h)

/-- Every exact boundary coefficient has a raw invariant lift solving all matching orders. -/
theorem originalSource_boundary_lift_matching_equations (t : Bsource) :
    ∃ a : Sinv, normalizedBoundaryChartMap f hL d V c k n o U hU a = t ∧
      ∀ order : ℕ,
        (rankPullbackMap (Over.mk p) endpoint n order ≫ F).appTop a.val =
          (rankPullbackMap (Over.mk p) endpoint n order ≫ H).appTop a.val := by
  obtain ⟨a, ha⟩ := normalizedBoundaryChartMap_surjective f hL d V c k n o U hU
    (show IsAffine U.toScheme from inferInstance) t
  exact ⟨a, ha, originalSource_relation_matching_equation f hL d V c k n o U hU a⟩

end FLT.Mazur.HilbertChart.AffineRestriction
