/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceBoundaryScalarCharts
public import FLT.Mazur.EquivalenceRelationScalarLocalRecovery
public import FLT.Mazur.EquivalenceRelationBoundaryGenericCharts

/-!
# Original Hilbert scalar residual maxima and bounded local stages

Every excluded original scalar prime has a maximal higher component bounded
by the original cutoff, with a finite stage recovering its entire generic
local chart. All points of the full scalar localization lift to bounded rank
stages on which the entire original source is finite. This is point coverage,
not the missing flat cover or coefficient descent across residual ranks.
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
local instance scalarMaximalChartNoetherian : IsNoetherian U.toScheme :=
  originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

open AffineScalarBoundaryNilpotence RelativeOrderedTuples
attribute [local irreducible] boundaryProduct boundaryCoordinate
local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ
local notation "prod" => chartBoundaryProduct n o U e hU σ κ
local instance scalarMaximalOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance scalarMaximalOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local notation "Cb" => Γ(boundaryProduct σ κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU σ κ
local notation "Itests" => boundaryTestIdeal σ κ tests

local instance scalarMaximalProjection_quasiFinite : LocallyQuasiFinite p :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)

/-- The scalar residual ceiling with Noetherianity derived from the original Hilbert source. -/
def originalSourceScalarRankCeiling (P : PrimeSpectrum Tsource) : ℕ := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact boundaryScalarRankCeiling n o U e hU σ κ P

local notation "ceiling" => originalSourceScalarRankCeiling f hL d V c k n o W U hU hUW

/-- The original cutoff bounds every point of the unchanged full scalar product. -/
theorem originalSource_product_rank_le_cutoff (pointZ : boundaryProduct σ κ) :
    rankOf pointZ ≤ originalFrameRankCutoff f hL d V c k := by
  obtain ⟨x, hx⟩ := chartBoundaryProduct_surjective n o U e hU σ κ pointZ
  have hRank := boundaryPointRank_spec n o U e hU σ κ pointZ
  rw [← hx] at hRank
  change x ∈ prod ⁻¹' boundaryExactRank n o U e hU σ κ (rankOf (prod x)) at hRank
  rw [boundaryExactRank_preimage] at hRank
  simpa only [hx] using originalFrameRankCutoff_spec f hL d V c k (bdy x) _ hRank.1

/-- Even absent scalar fibers have a controlled ceiling, with the frame size as baseline. -/
theorem originalSource_scalar_ceiling_bound (P : PrimeSpectrum Tsource) :
    ceiling P ≤ max n (originalFrameRankCutoff f hL d V c k) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  apply ScalarComponentRank.minimal _ _ n
    (boundary_component_ranks_bounded n o U e hU σ κ) P _ (le_max_left _ _)
  intro Q _
  exact (originalSource_product_rank_le_cutoff f hL d V c k n o W U hU hUW
    (boundaryComponentPoint σ κ Q)).trans (le_max_right _ _)

attribute [local irreducible] boundaryPointRank boundaryScalarRankCeiling
  boundaryGenericEndpoint boundaryScalarLocalProduct boundaryScalarLocalMap
  boundaryScalarLocalEndpoint boundaryScalarLocalRankMap boundaryComponentPoint
  boundaryScalarProjection boundaryScalarNilpotenceOpen completeAffineOrbitTests

/-- A maximal residual component has a bounded higher rank and a full generic local recovery. -/
theorem originalSource_scalar_maximal_residual_chart (P : PrimeSpectrum Tsource)
    (hP : P ∉ boundaryScalarNilpotenceOpen σ κ tests) :
    ∃ Q : minimalPrimes Cb,
      (boundaryScalarProjection σ κ (boundaryComponentPoint σ κ Q)).asIdeal ≤ P.asIdeal ∧
      n < rankOf (boundaryComponentPoint σ κ Q) ∧
      rankOf (boundaryComponentPoint σ κ Q) ≤ originalFrameRankCutoff f hL d V c k ∧
      rankOf (boundaryComponentPoint σ κ Q) = ceiling P ∧
      ∃ stage : ℕ, IsIso (rankPullbackMap (Over.mk p)
        (boundaryGenericEndpoint n o U e hU σ κ Q)
        (rankOf (boundaryComponentPoint σ κ Q)) stage) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  have hlt : n < boundaryScalarRankCeiling n o U e hU σ κ P := by
    apply lt_of_le_of_ne (boundaryScalarRankCeiling_ge n o U e hU σ κ P)
    exact Ne.symm fun h ↦ hP ((mem_boundaryScalarNilpotenceOpen_iff_ceiling
      n o U e hU σ κ P).mpr h)
  refine (boundaryScalarRankCeiling_attained n o U e hU σ κ P hlt).imp ?_
  intro Q hQ
  refine ⟨hQ.1, ?_,
    originalSource_product_rank_le_cutoff f hL d V c k n o W U hU hUW _, hQ.2.1,
    boundaryGeneric_rank_recovery n o U e hU σ κ Q⟩
  exact hlt.trans_eq hQ.2.1.symm

/-- Every original scalar-local point has a bounded stage with finite entire original source. -/
theorem originalSource_scalarLocal_finite_rank_stage (P : PrimeSpectrum Tsource) (powK : ℕ)
    (pointZ : boundaryScalarLocalProduct σ κ P) :
    ∃ (rankM : ℕ) (y : rankPullbackThickening (Over.mk p)
      (boundaryScalarLocalEndpoint n o U e hU σ κ P) rankM powK),
      n ≤ rankM ∧ rankM ≤ ceiling P ∧
      rankM ≤ originalFrameRankCutoff f hL d V c k ∧
      boundaryScalarLocalRankMap n o U e hU σ κ P rankM powK y = pointZ ∧
      IsFinite (pullback.snd p
        (rankPullbackMap (Over.mk p) (boundaryScalarLocalEndpoint n o U e hU σ κ P)
          rankM powK ≫ boundaryScalarLocalEndpoint n o U e hU σ κ P)) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  obtain ⟨rankM, y, hn, hb, hy⟩ :=
    exists_boundaryScalarLocal_rank_stage n o U e hU σ κ P powK pointZ
  have hRank := originalSource_product_rank_le_cutoff f hL d V c k n o W U hU hUW
    (boundaryScalarLocalMap σ κ P
      (boundaryScalarLocalRankMap n o U e hU σ κ P rankM powK y))
  rw [boundaryScalarLocalRankMap_rank] at hRank
  exact ⟨rankM, y, hn, hb, hRank, hy,
    boundaryScalarLocal_rank_stage_finite n o U e hU σ κ P rankM powK⟩

/-- Exclusion rules out every finite matching order on the full original scalar local chart. -/
theorem originalSource_scalarLocal_no_matching_recovery (P : PrimeSpectrum Tsource)
    (hP : P ∉ boundaryScalarNilpotenceOpen σ κ tests) (powK : ℕ) :
    ¬ IsIso (rankPullbackMap (Over.mk p)
      (boundaryScalarLocalEndpoint n o U e hU σ κ P) n powK) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact boundaryScalarLocal_matching_not_isIso n o U e hU σ κ P hP powK

/-- The maximal higher stage remains nonempty at every order over an excluded original prime. -/
theorem originalSource_scalarLocal_maximal_stage_nonempty (P : PrimeSpectrum Tsource)
    (hP : P ∉ boundaryScalarNilpotenceOpen σ κ tests) (powK : ℕ) :
    Nonempty (rankPullbackThickening (Over.mk p)
      (boundaryScalarLocalEndpoint n o U e hU σ κ P) (ceiling P) powK) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  apply boundaryScalarLocal_maximal_stage_nonempty n o U e hU σ κ P powK
  apply lt_of_le_of_ne (boundaryScalarRankCeiling_ge n o U e hU σ κ P)
  exact Ne.symm fun h ↦ hP ((mem_boundaryScalarNilpotenceOpen_iff_ceiling
    n o U e hU σ κ P).mpr h)

end FLT.Mazur.HilbertChart.AffineRestriction
