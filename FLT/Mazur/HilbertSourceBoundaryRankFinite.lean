/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceBoundaryComponentEquations
public import FLT.Mazur.HilbertSourceBoundaryTestNeighborhoods
public import FLT.Mazur.RelativeRankThickeningFinite

/-!
# Finite whole original sources on unsplit Hilbert boundary stages

Every full-product point has a bounded rank-stage lift where the entire original
relation projection is finite. All stage nilpotents are retained. This does not
make the stage map flat or cover the full product by matching-rank test orders.
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
local instance rankFiniteCompletenessNoetherian :
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
local instance rankFiniteHilbertOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance rankFiniteHilbertOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local instance rankFiniteHilbertOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ

local instance rankFiniteHilbertOver_quasiFinite : LocallyQuasiFinite (Over.mk p).hom :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)

omit [IsAffine U.toScheme] in
/-- Every original boundary rank stage has finite full original source, before frame splitting. -/
theorem originalSource_boundary_rankStage_finite (rankM powK : ℕ) :
    IsFinite (pullback.snd p
      (rankPullbackMap (Over.mk p) bdy rankM powK ≫ bdy)) :=
  finite_pullback_rankPullback (Over.mk p) bdy rankM powK

/-- Every full-product point lifts to a bounded stage with a finite entire original source. -/
theorem exists_originalSource_finite_boundary_rank_stage
    (powK : ℕ) (pointZ : boundaryProduct σ κ) :
    ∃ (rankM : ℕ) (y : rankPullbackThickening (Over.mk p) bdy rankM powK),
      n ≤ rankM ∧ rankM ≤ originalFrameRankCutoff f hL d V c k ∧
      boundaryRankProductMap n o U e hU σ κ powK rankM y = pointZ ∧
      IsFinite (pullback.snd p
        (rankPullbackMap (Over.mk p) bdy rankM powK ≫ bdy)) := by
  obtain ⟨rankM, y, hn, hb, hy⟩ := exists_originalSource_boundary_rank_stage
    f hL d V c k n o W U hU hUW powK pointZ
  exact ⟨rankM, y, hn, hb, hy,
    originalSource_boundary_rankStage_finite f hL d V c k n o W U hU hUW rankM powK⟩

/-- The full original relation is finite already on each unsplit boundary-test chart. -/
theorem originalSource_boundary_testChart_finite (powK : ℕ) :
    IsFinite (pullback.snd p (boundaryTestChartEndpoint n o U e hU σ κ powK)) := by
  apply finite_pullback_of_exactRank (Over.mk p) n
  rintro _ ⟨x, rfl⟩
  exact boundaryTestChartEndpoint_exactRank n o U e hU σ κ powK x

omit [IsAffine U.toScheme] in
/-- A stage meeting the nonfinite locus of the chart boundary cannot be flat over it. -/
theorem originalSource_boundary_rankStage_not_flat (rankM powK : ℕ)
    (x : rankPullbackThickening (Over.mk p) bdy rankM powK)
    (hx : rankPullbackMap (Over.mk p) bdy rankM powK x ∉
      SchemeOpenEnvelope.finiteTargetOpen (pullback.snd p bdy)) :
    ¬ Flat (rankPullbackMap (Over.mk p) bdy rankM powK) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact rankPullbackMap_not_flat (Over.mk p) bdy rankM powK x hx

end FLT.Mazur.HilbertChart.AffineRestriction
