/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceHigherScalarValuations
public import FLT.Mazur.AffineBoundaryTestGeneratorPoles
public import FLT.Mazur.SchemeFiniteGroupQuotientFiniteType

/-!
# Finite original test-chart generators and exact-center poles

Finite type of the original invariant scalar map is derived from the Hilbert
geometry and Artin--Tate. The full higher-rank principal charts therefore have
fixed finite scalar generators. Matching exact fibers turn any ceiling excess
into a pole of one of these generators at the unchanged original scalar prime.
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
local instance testGeneratorChartNoetherian : IsNoetherian U.toScheme :=
  originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

open AffineScalarBoundaryNilpotence RelativeOrderedTuples
attribute [local irreducible] boundaryProduct boundaryCoordinate
local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ
local notation "prod" => chartBoundaryProduct n o U e hU σ κ
local instance testGeneratorOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance testGeneratorOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local notation "Cb" => Γ(boundaryProduct σ κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU σ κ
local notation "Itests" => boundaryTestIdeal σ κ tests

local instance testGeneratorProjection_quasiFinite : LocallyQuasiFinite p :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)

local notation "ceiling" => originalSourceScalarRankCeiling f hL d V c k n o W U hU hUW
local notation "higher" => boundaryRankOpen n o U e hU σ κ (n + 1)
local notation "φ" => boundaryHigherScalarMap n o U e hU σ κ

/-- The original invariant-coordinate algebra is finite type over the unchanged scalar ring. -/
theorem originalSource_invariantScalar_finiteType : (σ).FiniteType := by
  let _ : LocallyOfFiniteType A.hom := by
    rw [← k.w]
    infer_instance
  let _ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let g := U.ι ≫ normalizedFullRelationFirst f hL d V c k n o ≫
    A.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ R))
  let _ : LocallyOfFiniteType g := by dsimp only [g]; infer_instance
  let _ := integerCoordinates_finiteType g
  let _ := invariantCoordinates_finiteType τU
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℤ Ω)
  have he : (σ).comp (algebraMap ℤ Ω) = algebraMap ℤ Sinv := Subsingleton.elim _ _
  rw [he]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

local notation "hfinite" => originalSource_invariantScalar_finiteType f hL d V c k n o W U hU hUW
local notation "testScalar" t:max => boundaryTestChartScalar σ κ t
local notation "generators" t:max => boundaryTestChartGenerators σ κ hfinite t
local notation "testMap" t:max => scalarMorphism (testScalar t)
open AffineValuationGeneratorLift

/-- All the original principal test charts have finite type over the original boundary scalars. -/
theorem originalSource_testChartScalar_finiteType (t : Sinv) :
    (testScalar t).FiniteType := boundaryTestChartScalar_finiteType σ κ t hfinite

/-- Exact-fiber rank equality gives test vanishing at every original fiber point. -/
theorem originalSource_matching_fiber_tests (P : PrimeSpectrum Tsource)
    (hf : ∀ pointZ : boundaryProduct σ κ,
      boundaryScalarProjection σ κ pointZ = P → rankOf pointZ = n) :
    ∀ pointZ : boundaryProduct σ κ, boundaryScalarProjection σ κ pointZ = P →
      ∀ t ∈ tests, t ∈ (boundaryProjection σ κ pointZ).asIdeal := by
  intro pointZ hz
  exact (boundaryTestIdeal_le_point_iff σ κ tests pointZ).mp
    ((boundaryTestIdeal_le_iff_matching_rank n o U e hU σ κ pointZ).mpr (hf pointZ hz))

/-- At a matching original fiber, higher computed rank forces a fixed finite-generator pole. -/
theorem originalSource_ceiling_excess_generator_pole (P : PrimeSpectrum Tsource)
    (hf : ∀ pointZ : boundaryProduct σ κ,
      boundaryScalarProjection σ κ pointZ = P → rankOf pointZ = n)
    (hp : n < ceiling P) :
    ∃ (t : tests) (S : ValuativeCommSq (testMap t.val)),
      S.i₂ (IsLocalRing.closedPoint S.R) = P ∧ ∃ coord ∈ generators t.val,
        genericCoordinates (testScalar t.val) S coord ∉ (algebraMap S.R S.K).range := by
  apply boundaryTestChart_exists_generator_pole σ κ hfinite tests P
    (originalSource_matching_fiber_tests f hL d V c k n o W U hU hUW P hf)
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact fun h ↦ hp.ne'
    ((mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU σ κ P).mp h)

/-- Finite-generator regularity at the exact center excludes all generizing higher components. -/
theorem originalSource_ceiling_eq_iff_test_regular (P : PrimeSpectrum Tsource)
    (hf : ∀ pointZ : boundaryProduct σ κ,
      boundaryScalarProjection σ κ pointZ = P → rankOf pointZ = n) :
    ceiling P = n ↔
      ∀ (t : tests) (S : ValuativeCommSq (testMap t.val)),
        S.i₂ (IsLocalRing.closedPoint S.R) = P → ∀ coord ∈ generators t.val,
          genericCoordinates (testScalar t.val) S coord ∈ (algebraMap S.R S.K).range := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact (mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU σ κ P).symm.trans
    (boundaryScalar_mem_iff_test_generators_regular σ κ hfinite tests P
      (originalSource_matching_fiber_tests f hL d V c k n o W U hU hUW P hf))

end FLT.Mazur.HilbertChart.AffineRestriction
