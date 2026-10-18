/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceBoundaryComponentEquations
public import FLT.Mazur.EquivalenceRelationBoundaryRankSeparation

/-!
# Constructed original Hilbert boundary rank stages

Every point of the full original scalar boundary product lifts to a thickened
rank stage between the chart size and the derived original cutoff. Matching
stages have nilpotent test ideals; higher stages have unit test ideals. The
remaining task is to exclude higher stages on the required residual charts.
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
local instance rankStageCompletenessNoetherian :
    TopologicalSpace.NoetherianSpace U.toScheme := by
  let _ := originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)
  infer_instance

open AffineScalarBoundaryNilpotence
attribute [local irreducible] boundaryProduct boundaryCoordinate
local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU
local notation "C" => U.ι ⁻¹' completePointLocus («p» := p) («q» := q) (Fin n) o

local notation "Cb" => Γ(boundaryProduct σ κ, ⊤)
open RelativeOrderedTuples
local instance rankStageHilbertOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance rankStageHilbertOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local instance rankStageHilbertOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ

/-- All original product points lift at every order, with an actual bounded original rank. -/
theorem exists_originalSource_boundary_rank_stage
    (powK : ℕ) (pointZ : boundaryProduct σ κ) :
    ∃ (rankM : ℕ) (y : rankPullbackThickening (Over.mk p) bdy rankM powK),
      n ≤ rankM ∧ rankM ≤ originalFrameRankCutoff f hL d V c k ∧
      boundaryRankProductMap n o U e hU σ κ powK rankM y = pointZ := by
  obtain ⟨rankM, y, hy⟩ := exists_boundary_rankThickening_lift n o U e hU σ κ powK pointZ
  have hn : n ≤ rankM := by
    by_contra hn
    exact (boundary_rankThickening_empty_below n o U e hU σ κ rankM powK
      (Nat.lt_of_not_ge hn)).false y
  have hRank := rankPullback_endpoint (Over.mk p) bdy rankM powK y
  exact ⟨rankM, y, hn, originalFrameRankCutoff_spec f hL d V c k _ rankM hRank.1, hy⟩

/-- Matching original stages have actual ideal-power equations on compact coefficient charts. -/
theorem originalSource_matching_rankStage_testIdeal_nilpotent (powK : ℕ)
    {Y : Scheme.{0}} [CompactSpace Y]
    (v : Y ⟶ rankPullbackThickening (Over.mk p) bdy n powK) :
    IsNilpotent ((boundaryTestIdeal σ κ tests).map
      (v ≫ boundaryRankProductMap n o U e hU σ κ powK n).appTop.hom) :=
  boundaryRank_testIdeal_nilpotent n o U e hU σ κ powK v

/-- Higher original stages have a unit test ideal, even with all their nilpotents retained. -/
theorem originalSource_higher_rankStage_testIdeal_top (powK rankM : ℕ) (hm : n < rankM)
    {Y : Scheme.{0}} [IsAffine Y]
    (v : Y ⟶ rankPullbackThickening (Over.mk p) bdy rankM powK) :
    (boundaryTestIdeal σ κ tests).map
      (v ≫ boundaryRankProductMap n o U e hU σ κ powK rankM).appTop.hom = ⊤ :=
  boundaryRank_higher_testIdeal_top n o U e hU σ κ powK rankM hm v

end FLT.Mazur.HilbertChart.AffineRestriction
