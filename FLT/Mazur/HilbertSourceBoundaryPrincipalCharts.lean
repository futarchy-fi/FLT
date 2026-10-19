/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceBoundaryGenericCharts
public import FLT.Mazur.EquivalenceRelationBoundaryPrincipalCharts

/-!
# Principal matching neighborhoods for original Hilbert components

Matching minimal components now have actual principal neighborhoods with
finite flat faithful charts and finite matching-stage recovery. The remaining
closed set is the closure of higher original ranks in the unchanged product.
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


variable [IsAffine U.toScheme]
local instance principalOriginalChartNoetherian : IsNoetherian U.toScheme :=
  originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

open AffineScalarBoundaryNilpotence RelativeOrderedTuples
attribute [local irreducible] boundaryProduct boundaryCoordinate
local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ
local notation "prod" => chartBoundaryProduct n o U e hU σ κ
local instance principalOriginalOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance principalOriginalOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local notation "Cb" => Γ(boundaryProduct σ κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU σ κ
local notation "Itests" => boundaryTestIdeal σ κ tests

/-- The original residual closed set is exactly the closure of higher computed ranks. -/
theorem originalSource_boundaryNilpotenceOpen_compl :
    (boundaryNilpotenceOpen σ κ tests : Set (boundaryProduct σ κ))ᶜ =
      closure {pointZ : boundaryProduct σ κ | n < rankOf pointZ} :=
  boundaryNilpotenceOpen_compl_eq_higher_closure n o U e hU σ κ

attribute [local irreducible] boundaryPointRank boundaryComponentPoint boundaryTestIdeal
  boundaryPrincipalProjection boundaryPrincipalEndpoint

/-- Matching original components supply coefficient denominators annihilating test powers. -/
theorem originalSource_matching_component_denominator
    (Q : minimalPrimes Cb) (hQ : rankOf (boundaryComponentPoint σ κ Q) = n) :
    ∃ (order : ℕ) (u : Cb), u ∉ Q.val ∧ u ∈ (Itests ^ order).annihilator ∧
      ((Itests).map (algebraMap Cb (Localization.Away u))) ^ order = ⊥ :=
  boundary_matching_component_denominator n o U e hU σ κ Q hQ

/-- The principal chart is a faithful cover of the full original coefficient neighborhood. -/
theorem originalSource_boundaryPrincipal_effectiveEpi (u : Cb) :
    EffectiveEpi (boundaryPrincipalProjection n o U e hU σ κ u) := inferInstance

/-- A certified principal chart recovers a finite matching stage under the original hypotheses. -/
theorem originalSource_boundaryPrincipal_rank_recovery
    (order : ℕ) (u : Cb) (hu : u ∈ (Itests ^ order).annihilator) :
    ∃ stage : ℕ, IsIso (rankPullbackMap (Over.mk p)
      (boundaryPrincipalEndpoint n o U e hU σ κ u) n stage) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact boundaryPrincipal_rank_recovery n o U e hU σ κ u order hu

/-- Every point of the certified principal neighborhood keeps the exact original frame size. -/
theorem originalSource_principal_point_rank
    (order : ℕ) (u : Cb) (hu : u ∈ (Itests ^ order).annihilator)
    (pointZ : boundaryProduct σ κ)
    (hz : u ∉ ((boundaryProduct σ κ).isoSpec.hom pointZ).asIdeal) : rankOf pointZ = n :=
  boundary_rank_eq_of_power_annihilator n o U e hU σ κ order u hu pointZ hz

/-- At the derived original cutoff, the actual nilpotence open is the whole original product. -/
theorem originalSource_boundaryNilpotenceOpen_eq_top_of_cutoff
    (hn : originalFrameRankCutoff f hL d V c k ≤ n) :
    boundaryNilpotenceOpen σ κ tests = ⊤ := by
  apply (boundaryNilpotenceOpen_eq_top_iff σ κ tests).mpr
  apply (boundary_nilpotent_iff_pointRank n o U e hU σ κ).mpr
  intro pointZ
  obtain ⟨hlo, hhi⟩ := originalSource_boundaryPointRank_bounds
    f hL d V c k n o W U hU hUW pointZ
  exact Nat.le_antisymm (hhi.trans hn) hlo

end FLT.Mazur.HilbertChart.AffineRestriction
