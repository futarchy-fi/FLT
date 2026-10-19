/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceResidualRankLifts

/-!
# Finite persistent witnesses to failure of original residual corrections

A failed correction has a bounded higher rank and a finite ideal-power order
where its discrepancy remains. It remains at every larger order. Failure of
the original localized source map gives a single raw lift for which every
allowed scalar and every boundary-zero correction has such a witness.
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
local notation "boundaryOrbitMap" => originalClosedInvariantMap f hL d V c k
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
local notation "Wc" => (TopologicalSpace.Opens.map (boundaryOrbitMap).base).obj W
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


open RelativeOrderedTuples
attribute [local irreducible] originalSourceCompatibleModule
local notation "endpoint" => F ≫ kS
local notation "cutoff" => originalFrameRankCutoff f hL d V c k
local notation "good" => originalSourceGoodRelationOpen f hL d V c k n o U hU
local notation "Csource" => originalSourceCompatibleModule f hL d V c k n o W U hU hUW
local instance residualObstructionOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance residualObstructionOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)


local notation "β" => normalizedBoundaryChartMap f hL d V c k n o U hU


local notation "Δ" => originalSourceRankDiscrepancy f hL d V c k n o U hU
local notation "βsource" => originalSourceCompatibleBoundaryMap f hL d V c k n o W U hU hUW


/-- A discrepancy detected at one order survives every larger original ideal-power order. -/
theorem originalSourceRankDiscrepancy_persists (a w : Sinv) (m order : ℕ)
    (hne : Δ m order a ≠ Δ m order w) (later : ℕ) (h : order ≤ later) :
    Δ m later a ≠ Δ m later w := by
  intro he
  apply hne
  let transition := rankStagePullbackTransition (Over.mk p) endpoint m h
  have hf : transition ≫ rankPullbackMap (Over.mk p) endpoint m later ≫ F =
      rankPullbackMap (Over.mk p) endpoint m order ≫ F :=
    rankStagePullbackTransition_map_assoc (Over.mk p) endpoint m h F
  have hh : transition ≫ rankPullbackMap (Over.mk p) endpoint m later ≫ H =
      rankPullbackMap (Over.mk p) endpoint m order ≫ H :=
    rankStagePullbackTransition_map_assoc (Over.mk p) endpoint m h H
  have hz := congrArg (fun coeff ↦ transition.appTop coeff) he
  change transition.appTop (_ - _) = transition.appTop (_ - _) at hz
  simp only [map_sub] at hz
  change (transition ≫ rankPullbackMap (Over.mk p) endpoint m later ≫ F).appTop a.val -
      (transition ≫ rankPullbackMap (Over.mk p) endpoint m later ≫ H).appTop a.val =
    (transition ≫ rankPullbackMap (Over.mk p) endpoint m later ≫ F).appTop w.val -
      (transition ≫ rankPullbackMap (Over.mk p) endpoint m later ≫ H).appTop w.val at hz
  rw [hf, hh] at hz
  exact hz

variable [IsAffine U.toScheme]

/-- Any failed residual correction has a finite higher-rank witness that persists. -/
theorem originalSource_failed_correction_persistent_witness (a w : Sinv)
    (ha : let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
      a - w ∉ Csource) :
    ∃ m : ℕ, n < m ∧ m ≤ cutoff ∧ ∃ order : ℕ,
      ∀ later : ℕ, order ≤ later → Δ m later a ≠ Δ m later w := by
  have hn : ¬ ∀ m : ℕ, n < m → m ≤ cutoff → ∀ order : ℕ,
      Δ m order a = Δ m order w := by
    intro h
    exact ha ((originalSource_correction_iff_higher_discrepancies
      f hL d V c k n o W U hU hUW a w).mpr h)
  push Not at hn
  obtain ⟨m, hm, hM, order, hne⟩ := hn
  exact ⟨m, hm, hM, order,
    originalSourceRankDiscrepancy_persists f hL d V c k n o U hU a w m order hne⟩

/-- Failure at an unchanged source prime forces persistent defects for every allowed correction. -/
theorem originalSource_not_surjective_residual_witness
    (P : Ideal Tsource) [P.IsPrime]
    (hP : let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
      let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
      ¬ Function.Surjective
        (originalSourceLocalizedCompatibleBoundaryMap f hL d V c k n o W U hU hUW P)) :
    ∃ a : Sinv, ∀ x : Ω, κ x ∉ P → ∀ w : Sinv, β w = 0 →
      ∃ m : ℕ, n < m ∧ m ≤ cutoff ∧ ∃ order : ℕ,
        ∀ later : ℕ, order ≤ later → Δ m later (σ x * a) ≠ Δ m later w := by
  have h := (originalSource_surjective_iff_residual_corrections
    f hL d V c k n o W U hU hUW P).not.mp hP
  push Not at h
  obtain ⟨a, ha⟩ := h
  refine ⟨a, fun x hx w hw ↦ ?_⟩
  obtain ⟨m, hm, hM, order, hne⟩ := ha x hx w hw
  exact ⟨m, hm, hM, order,
    originalSourceRankDiscrepancy_persists f hL d V c k n o U hU
      (σ x * a) w m order hne⟩

end FLT.Mazur.HilbertChart.AffineRestriction
