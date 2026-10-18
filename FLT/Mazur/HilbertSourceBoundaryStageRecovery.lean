/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceBoundaryRankNilpotence
public import FLT.Mazur.EquivalenceRelationBoundaryRankRecovery
public import FLT.Mazur.EquivalenceRelationBoundaryTestFactorization

/-!
# Finite-order recovery on the original Hilbert boundary

The original Hilbert assumptions construct finite matching-rank factorizations
of every test neighborhood. Recovery of the entire chart boundary is exactly
the still-required full-product test nilpotence. At the original global rank
cutoff the equations and the recovery are unconditional.
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
local instance rankRecoveryCompletenessNoetherian :
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
local instance rankRecoveryHilbertOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance rankRecoveryHilbertOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local instance rankRecoveryHilbertOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ



local instance originalStageTestCompact (powK : ℕ) :
    CompactSpace (boundaryTestChart n o U e hU σ κ powK) := by
  let _ : IsAffine (boundaryTestThickening σ κ tests powK) :=
    isAffine_of_isAffineHom (boundaryTestThickeningMap σ κ tests powK)
  change CompactSpace (Limits.pullback («C» := Scheme) (SchemeFiniteGroupQuotient.quotientMap τU)
    (boundaryTestThickeningMap σ κ tests powK ≫ boundaryProjection σ κ))
  infer_instance

/-- Every original test chart factors as a scheme through a finite matching original rank stage. -/
theorem originalSource_testChart_finite_rank_factor (powK : ℕ) :
    ∃ (order : ℕ) (w : boundaryTestChart n o U e hU σ κ powK ⟶
        rankPullbackThickening (Over.mk p) bdy n order),
      w ≫ rankPullbackMap (Over.mk p) bdy n order =
        boundaryTestChartMap n o U e hU σ κ powK := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  simpa only [Category.id_comp] using
    exists_boundaryTestChart_rank_factor n o U e hU σ κ powK (𝟙 _)

/-- A high enough original rank order recovers every coefficient of the test chart. -/
theorem originalSource_testChart_rank_recovery (powK : ℕ) :
    ∃ order : ℕ, IsIso (rankPullbackMap (Over.mk p)
      (boundaryTestChartEndpoint n o U e hU σ κ powK) n order) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  apply exists_rankPullbackMap_isIso
  rintro _ ⟨y, rfl⟩
  exact boundaryTestChartEndpoint_exactRank n o U e hU σ κ powK y

/-- Recovery of the full chart boundary is equivalent to the actual original test equations. -/
theorem originalSource_boundary_nilpotent_iff_rank_recovery :
    IsNilpotent (boundaryTestIdeal σ κ tests) ↔
      ∃ order : ℕ, IsIso (rankPullbackMap (Over.mk p) bdy n order) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact boundaryTestIdeal_nilpotent_iff_rankStage_isIso n o U e hU σ κ

/-- At the original rank cutoff a finite matching stage recovers the full chart boundary. -/
theorem originalSource_boundary_rank_recovery_of_cutoff
    (hn : originalFrameRankCutoff f hL d V c k ≤ n) :
    ∃ order : ℕ, IsIso (rankPullbackMap (Over.mk p) bdy n order) := by
  apply (originalSource_boundary_nilpotent_iff_rank_recovery
    f hL d V c k n o W U hU hUW).mp
  exact (boundaryTestIdeal_nilpotent_iff σ κ tests).mpr
    (originalSource_boundary_nilpotent_of_rankCutoff f hL d V c k n o W U hU hUW hn)

end FLT.Mazur.HilbertChart.AffineRestriction
