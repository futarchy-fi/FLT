/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceTestKernelObstruction
public import FLT.Mazur.AffineBoundaryTestKernelDescent
public import FLT.Mazur.SchemeFiniteGroupQuotientFiniteType

/-!
# Finite fppf equation descent on original Hilbert residual charts

Equations in full rings of finite fppf branches descend to original scalar
rank exclusion. A proved comaximality certificate gives one scalar equal to
one on a whole residual locus and annihilating an entire original test power.
The equations and comaximality remain obligations of residual geometry.
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
local instance testDescentChartNoetherian : IsNoetherian U.toScheme :=
  originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

open AffineScalarBoundaryNilpotence RelativeOrderedTuples
attribute [local irreducible] boundaryProduct boundaryCoordinate
local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ
local notation "prod" => chartBoundaryProduct n o U e hU σ κ
local instance testDescentOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance testDescentOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local notation "Cb" => Γ(boundaryProduct σ κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU σ κ
local notation "Itests" => boundaryTestIdeal σ κ tests

local instance testDescentProjection_quasiFinite : LocallyQuasiFinite p :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)

local notation "ceiling" => originalSourceScalarRankCeiling f hL d V c k n o W U hU hUW
local notation "higher" => boundaryRankOpen n o U e hU σ κ (n + 1)
local notation "φ" => boundaryHigherScalarMap n o U e hU σ κ

/-- Independent equations on actual finite fppf branches exclude all generizing higher ranks. -/
theorem originalSource_ceiling_eq_of_fppf_test_equations
    (C : Scheme.Cover.{0} Scheme.fppfPrecoverage (boundaryProduct σ κ)) [Finite C.I₀]
    (P : PrimeSpectrum Tsource)
    (h : ∀ t ∈ tests, ∀ idx, ∃ (x : Tsource) (order : ℕ), x ∉ P.asIdeal ∧
      ((C.f idx).appTop (boundaryCoordinate σ κ t)) ^ order *
        (C.f idx).appTop (boundaryScalarHom σ κ x) = 0) : ceiling P = n := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  apply (mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU σ κ P).mp
  exact boundaryScalar_mem_of_fppf_equations σ κ C tests P h

/-- Finite branch equations construct a full original matching-rank neighborhood. -/
theorem originalSource_rank_chart_of_fppf_test_equations
    (C : Scheme.Cover.{0} Scheme.fppfPrecoverage (boundaryProduct σ κ)) [Finite C.I₀]
    (P : PrimeSpectrum Tsource)
    (h : ∀ t ∈ tests, ∀ idx, ∃ (x : Tsource) (order : ℕ), x ∉ P.asIdeal ∧
      ((C.f idx).appTop (boundaryCoordinate σ κ t)) ^ order *
        (C.f idx).appTop (boundaryScalarHom σ κ x) = 0) :
    ∃ t : Tsource, t ∉ P.asIdeal ∧ ∃ stage : ℕ,
      IsIso (rankPullbackMap (Over.mk p)
        (boundaryPrincipalEndpoint n o U e hU σ κ (boundaryScalarHom σ κ t)) n stage) := by
  apply originalSource_scalar_rank_chart f hL d V c k n o W U hU hUW P
  exact boundaryScalar_mem_of_fppf_equations σ κ C tests P h

/-- A residual comaximality certificate constructs one original scalar normalized on that locus. -/
theorem originalSource_residual_test_denominator (J : Ideal Tsource)
    (h : originalSourceTestKernelIdeal f hL d V c k n o W U hU hUW ⊔ J = ⊤) :
    ∃ (x : Tsource) (order : ℕ), 1 - x ∈ J ∧
      boundaryScalarHom σ κ x ∈ (Itests ^ order).annihilator ∧
      ∀ P : PrimeSpectrum Tsource, J ≤ P.asIdeal → x ∉ P.asIdeal := by
  apply boundaryScalar_residual_uniform_denominator σ κ tests J
  intro P hp
  apply (boundaryScalar_mem_iff_testKernelProduct σ κ tests P).mpr
  intro hk
  have ht : (⊤ : Ideal Tsource) ≤ P.asIdeal := h ▸ sup_le hk hp
  exact P.isPrime.ne_top (top_le_iff.mp ht)

end FLT.Mazur.HilbertChart.AffineRestriction
