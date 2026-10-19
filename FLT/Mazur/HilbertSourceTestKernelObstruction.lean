/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceHigherScalarValuations
public import FLT.Mazur.AffineBoundaryTestKernels
public import FLT.Mazur.SchemeFiniteGroupQuotientFiniteType

/-!
# A computed scalar equation ideal for original Hilbert rank exclusion

The finite product of actual principal-chart kernels defines the entire
original higher-rank obstruction. Independent original scalar equations on
these charts multiply to a denominator killing a full completeness-test power.
Required residual-prime avoidance is not assumed or proved here.
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
local instance testKernelChartNoetherian : IsNoetherian U.toScheme :=
  originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

open AffineScalarBoundaryNilpotence RelativeOrderedTuples
attribute [local irreducible] boundaryProduct boundaryCoordinate
local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ
local notation "prod" => chartBoundaryProduct n o U e hU σ κ
local instance testKernelOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance testKernelOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local notation "Cb" => Γ(boundaryProduct σ κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU σ κ
local notation "Itests" => boundaryTestIdeal σ κ tests

local instance testKernelProjection_quasiFinite : LocallyQuasiFinite p :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)

local notation "ceiling" => originalSourceScalarRankCeiling f hL d V c k n o W U hU hUW
local notation "higher" => boundaryRankOpen n o U e hU σ κ (n + 1)
local notation "φ" => boundaryHigherScalarMap n o U e hU σ κ

/-- The original scalar equation ideal from the finite full principal test atlas. -/
def originalSourceTestKernelIdeal : Ideal Tsource :=
  boundaryTestKernelProduct σ κ tests

local notation "Jtests" => originalSourceTestKernelIdeal f hL d V c k n o W U hU hUW

/-- The computed ideal detects the ceiling on all generizing components, without a fiber input. -/
theorem originalSource_ceiling_eq_iff_testKernel (P : PrimeSpectrum Tsource) :
    ceiling P = n ↔ ¬ Jtests ≤ P.asIdeal := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact (mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU σ κ P).symm.trans
    (boundaryScalar_mem_iff_testKernelProduct σ κ tests P)

/-- Higher original rank is precisely membership in the closed computed scalar obstruction. -/
theorem originalSource_ceiling_excess_iff_testKernel (P : PrimeSpectrum Tsource) :
    n < ceiling P ↔ Jtests ≤ P.asIdeal := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  have hn := boundaryScalarRankCeiling_ge n o U e hU σ κ P
  have he := originalSource_ceiling_eq_iff_testKernel f hL d V c k n o W U hU hUW P
  constructor
  · intro h
    by_contra hp
    exact h.ne' (he.mpr hp)
  · intro hp
    apply lt_of_le_of_ne hn
    exact Ne.symm fun h ↦ he.mp h hp

/-- Original scalar equations on each chart yield the product scalar and a whole-power equation. -/
theorem originalSource_testKernel_product_denominator (P : PrimeSpectrum Tsource)
    (x : Sinv → Tsource) (hx : ∀ t ∈ tests, x t ∉ P.asIdeal)
    (he : ∀ t ∈ tests, x t ∈ boundaryTestKernel σ κ t) :
    (∏ t ∈ tests, x t) ∉ P.asIdeal ∧
      ∃ order : ℕ, boundaryScalarHom σ κ (∏ t ∈ tests, x t) ∈
        (Itests ^ order).annihilator :=
  boundary_product_chart_equations σ κ tests P x hx he

/-- Exact original kernel equations exclude higher ranks; no scalar is replaced by a cutoff. -/
theorem originalSource_ceiling_eq_of_testKernel_equations (P : PrimeSpectrum Tsource)
    (h : ∀ t ∈ tests, ∃ x : Tsource, x ∉ P.asIdeal ∧
      boundaryTestChartScalar σ κ t x = 0) : ceiling P = n := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  apply (mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU σ κ P).mp
  apply (boundaryScalar_mem_iff_testKernels σ κ tests P).mpr
  intro t ht hle
  obtain ⟨x, hx, he⟩ := h t ht
  exact hx (hle he)

/-- The constructed chart equations give an actual whole matching-rank neighborhood. -/
theorem originalSource_rank_chart_of_testKernel_equations (P : PrimeSpectrum Tsource)
    (h : ∀ t ∈ tests, ∃ x : Tsource, x ∉ P.asIdeal ∧
      boundaryTestChartScalar σ κ t x = 0) :
    ∃ t : Tsource, t ∉ P.asIdeal ∧ ∃ stage : ℕ,
      IsIso (rankPullbackMap (Over.mk p)
        (boundaryPrincipalEndpoint n o U e hU σ κ (boundaryScalarHom σ κ t)) n stage) := by
  apply originalSource_scalar_rank_chart f hL d V c k n o W U hU hUW P
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  apply (mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU σ κ P).mpr
  exact originalSource_ceiling_eq_of_testKernel_equations f hL d V c k n o W U hU hUW P h

end FLT.Mazur.HilbertChart.AffineRestriction
