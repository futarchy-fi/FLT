/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceScalarResidualStages
public import FLT.Mazur.EquivalenceRelationHigherScalarValuations

/-!
# Exact-center higher-rank valuations on original Hilbert scalar charts

Original scalar rank excess constructs actual valuation squares of the higher
open, including an original minimal component. Matching exact fibers and
extension of these squares would exclude all higher generizing components.
The extension input remains a geometric obligation, not an assumed record.
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
local instance higherValuationChartNoetherian : IsNoetherian U.toScheme :=
  originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

open AffineScalarBoundaryNilpotence RelativeOrderedTuples
attribute [local irreducible] boundaryProduct boundaryCoordinate
local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ
local notation "prod" => chartBoundaryProduct n o U e hU σ κ
local instance higherValuationOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance higherValuationOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local notation "Cb" => Γ(boundaryProduct σ κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU σ κ
local notation "Itests" => boundaryTestIdeal σ κ tests

local instance higherValuationProjection_quasiFinite : LocallyQuasiFinite p :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)

local notation "ceiling" => originalSourceScalarRankCeiling f hL d V c k n o W U hU hUW
local notation "higher" => boundaryRankOpen n o U e hU σ κ (n + 1)
local notation "φ" => boundaryHigherScalarMap n o U e hU σ κ

/-- Excess of the unchanged original ceiling is detected by exact-center valuation squares. -/
theorem originalSource_ceiling_excess_iff_square (P : PrimeSpectrum Tsource) :
    n < ceiling P ↔
      ∃ S : ValuativeCommSq φ, S.i₂ (IsLocalRing.closedPoint S.R) = P := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  rw [boundaryHigherScalar_square_iff]
  constructor
  · intro h hp
    have he := (mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU σ κ P).mp hp
    exact h.ne' he
  · intro hp
    apply lt_of_le_of_ne (boundaryScalarRankCeiling_ge n o U e hU σ κ P)
    exact Ne.symm fun he ↦ hp
      ((mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU σ κ P).mpr he)

/-- A failed original residual prime has an exact-center square at a higher minimal component. -/
theorem originalSource_higher_component_square (P : PrimeSpectrum Tsource)
    (hP : n < ceiling P) :
    ∃ (Q : minimalPrimes Cb) (S : ValuativeCommSq φ),
      (higher).ι (S.i₁ default) = boundaryComponentPoint σ κ Q ∧
      S.i₂ (IsLocalRing.closedPoint S.R) = P := by
  have hp : P ∉ boundaryScalarNilpotenceOpen σ κ tests := by
    let _ := selectedAffineHilbertSource_isNoetherian f d V k
    intro hp
    exact hP.ne' ((mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU σ κ P).mp hp)
  exact boundaryHigherScalar_component_square n o U e hU σ κ P hp

/-- Matching at the exact original fiber leaves a concrete nonextendible higher-rank square. -/
theorem originalSource_higher_square_no_lift (P : PrimeSpectrum Tsource)
    (hP : n < ceiling P)
    (hf : ∀ pointZ : boundaryProduct σ κ,
      boundaryScalarProjection σ κ pointZ = P → rankOf pointZ = n) :
    ∃ S : ValuativeCommSq φ,
      S.i₂ (IsLocalRing.closedPoint S.R) = P ∧ ¬ S.commSq.HasLift := by
  obtain ⟨S, hS⟩ := (originalSource_ceiling_excess_iff_square f hL d V c k n o W U hU hUW P).mp hP
  exact ⟨S, hS, boundaryHigherScalar_no_lift n o U e hU σ κ P hf S hS⟩

/-- Extending the actual higher-rank tests at a matching center excludes every higher component. -/
theorem originalSource_ceiling_eq_of_higher_lifts (P : PrimeSpectrum Tsource)
    (hf : ∀ pointZ : boundaryProduct σ κ,
      boundaryScalarProjection σ κ pointZ = P → rankOf pointZ = n)
    (hl : ∀ S : ValuativeCommSq φ,
      S.i₂ (IsLocalRing.closedPoint S.R) = P → S.commSq.HasLift) : ceiling P = n := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact (mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU σ κ P).mp
    (boundaryScalar_mem_of_higher_lifts n o U e hU σ κ P hf hl)

/-- These exact-center geometric tests yield an actual original matching neighborhood. -/
theorem originalSource_rank_chart_of_higher_lifts (P : PrimeSpectrum Tsource)
    (hf : ∀ pointZ : boundaryProduct σ κ,
      boundaryScalarProjection σ κ pointZ = P → rankOf pointZ = n)
    (hl : ∀ S : ValuativeCommSq φ,
      S.i₂ (IsLocalRing.closedPoint S.R) = P → S.commSq.HasLift) :
    ∃ t : Tsource, t ∉ P.asIdeal ∧ ∃ stage : ℕ,
      IsIso (rankPullbackMap (Over.mk p)
        (boundaryPrincipalEndpoint n o U e hU σ κ (boundaryScalarHom σ κ t)) n stage) := by
  apply originalSource_scalar_rank_chart f hL d V c k n o W U hU hUW P
  exact boundaryScalar_mem_of_higher_lifts n o U e hU σ κ P hf hl

end FLT.Mazur.HilbertChart.AffineRestriction
