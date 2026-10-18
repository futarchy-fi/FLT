/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceBoundaryStageRecovery
public import FLT.Mazur.EquivalenceRelationBoundaryUniformOrders

/-!
# Uniform orders for the unchanged original Hilbert boundary

Original Hilbert geometry supplies the Noetherian chart on which the rank and
test order constants are constructed. No extra assumption is made on Tsource.
The derived order recovers the full chart when an actual test-power equation
has been established; it does not assert that equation on residual charts.
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
local instance uniformOriginalChartNoetherian : IsNoetherian U.toScheme :=
  originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

open AffineScalarBoundaryNilpotence RelativeOrderedTuples
attribute [local irreducible] boundaryProduct boundaryCoordinate
local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ
local notation "prod" => chartBoundaryProduct n o U e hU σ κ
local instance uniformOriginalOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance uniformOriginalOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

/-- Original Hilbert rank-stage kernels and test powers have uniform linear order comparisons. -/
theorem originalSource_boundary_rank_test_orders :
    ∃ c d : ℕ, 0 < c ∧ 0 < d ∧ ∀ powK : ℕ,
      (rankPullbackMap (Over.mk p) bdy n powK).ker ^ c ≤
        (boundaryTestSheaf σ κ tests).comap prod ^ (powK + 1) ∧
      (boundaryTestSheaf σ κ tests).comap prod ^ (d * (powK + 1)) ≤
        (rankPullbackMap (Over.mk p) bdy n powK).ker := by
  obtain ⟨c, d, hc, hd, h⟩ := boundary_rank_test_uniform_orders n o U e hU
  exact ⟨c, d, hc, hd, h _ _ σ κ⟩

/-- A proved original test equation gives a computed order recovering every chart coefficient. -/
theorem originalSource_boundary_uniform_recovery_order :
    ∃ c : ℕ, 0 < c ∧ ∀ powK : ℕ,
      (boundaryTestSheaf σ κ tests).comap prod ^ (powK + 1) = ⊥ →
        IsIso (rankPullbackMap (Over.mk p) bdy n (c * (powK + 1) - 1)) :=
  boundary_rank_recovery_uniform_order n o U e hU σ κ


/-- An actual full-product equation computes a finite rank order without reducing Tsource. -/
theorem originalSource_boundary_product_power_recovery :
    ∃ c : ℕ, 0 < c ∧ ∀ powK : ℕ,
      boundaryTestIdeal σ κ tests ^ (powK + 1) = ⊥ →
        IsIso (rankPullbackMap (Over.mk p) bdy n (c * (powK + 1) - 1)) :=
  boundary_rank_recovery_of_product_power n o U e hU σ κ

end FLT.Mazur.HilbertChart.AffineRestriction
