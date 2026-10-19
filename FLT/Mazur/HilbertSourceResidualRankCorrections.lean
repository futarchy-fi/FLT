/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceResidualRankCompatibility

/-!
# Boundary-preserving corrections detected on higher ranks

Construct the discrepancy maps from actual full relation stages. A correction
in the unchanged boundary kernel removes a raw lift's discrepancy exactly when
it does so at every bounded higher rank and order. Matching equations hold
unconditionally; existence of the required corrections is a separate task.
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
local instance residualCorrectionOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance residualCorrectionOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)


local notation "β" => normalizedBoundaryChartMap f hL d V c k n o U hU

/-- The additive discrepancy on an actual original rank thickening, before any reduction. -/
def originalSourceRankDiscrepancy (m order : ℕ) :
    Sinv →+ Γ(rankPullbackThickening (Over.mk p) endpoint m order, ⊤) :=
  (((rankPullbackMap (Over.mk p) endpoint m order ≫ F).appTop.hom).comp
    (Subring.subtype _)).toAddMonoidHom -
  (((rankPullbackMap (Over.mk p) endpoint m order ≫ H).appTop.hom).comp
    (Subring.subtype _)).toAddMonoidHom

local notation "Δ" => originalSourceRankDiscrepancy f hL d V c k n o U hU

/-- Discrepancy zero is the full original two-endpoint equation on this thickened stage. -/
theorem originalSourceRankDiscrepancy_eq_zero (m order : ℕ) (a : Sinv) :
    Δ m order a = 0 ↔
      (rankPullbackMap (Over.mk p) endpoint m order ≫ F).appTop a.val =
        (rankPullbackMap (Over.mk p) endpoint m order ≫ H).appTop a.val :=
  sub_eq_zero

/-- Every raw invariant numerator has zero discrepancy at all matching orders. -/
theorem originalSourceRankDiscrepancy_matching (order : ℕ) (a : Sinv) :
    Δ n order a = 0 :=
  (originalSourceRankDiscrepancy_eq_zero f hL d V c k n o U hU n order a).mpr
    (originalSource_relation_matching_equation f hL d V c k n o U hU a order)

variable [IsAffine U.toScheme]

/-- Subtracting a correction is compatible exactly when its residual rows match. -/
theorem originalSource_correction_iff_higher_discrepancies (a w : Sinv) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    a - w ∈ Csource ↔ ∀ m : ℕ, n < m → m ≤ cutoff → ∀ order : ℕ,
      Δ m order a = Δ m order w := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  refine (originalSource_mem_iff_higher_rank_equations
    f hL d V c k n o W U hU hUW (a - w)).trans ?_
  apply forall_congr'
  intro m
  apply forall_congr'
  intro _
  apply forall_congr'
  intro _
  apply forall_congr'
  intro order
  rw [← originalSourceRankDiscrepancy_eq_zero, map_sub, sub_eq_zero]

/-- Compatible lifts of a fixed boundary value are residual corrections of any raw lift. -/
theorem originalSource_lift_iff_residual_correction (a : Sinv) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    (∃ v : Sinv, v ∈ Csource ∧ β v = β a) ↔
      ∃ w : Sinv, β w = 0 ∧ ∀ m : ℕ, n < m → m ≤ cutoff → ∀ order : ℕ,
        Δ m order a = Δ m order w := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  constructor
  · rintro ⟨v, hv, hb⟩
    refine ⟨a - v, by rw [map_sub, hb, sub_self], ?_⟩
    apply (originalSource_correction_iff_higher_discrepancies
      f hL d V c k n o W U hU hUW a (a - v)).mp
    simpa only [sub_sub_cancel] using hv
  · rintro ⟨w, hw, hΔ⟩
    refine ⟨a - w, (originalSource_correction_iff_higher_discrepancies
      f hL d V c k n o W U hU hUW a w).mpr hΔ, ?_⟩
    rw [map_sub, hw, sub_zero]

end FLT.Mazur.HilbertChart.AffineRestriction
