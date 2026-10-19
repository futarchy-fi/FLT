/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceResidualRankCorrections
public import FLT.Mazur.HilbertSourceCoefficientwiseSurjectivity

/-!
# Original scalar localized lifts from residual correction equations

The original localized source map is surjective exactly when each raw lift
admits a boundary-zero correction after multiplication by an allowed original
scalar. Only bounded higher-rank equations have to be solved. A finite family
of such corrections assembles to one scalar and a linear lift of its free
module of generators; relations remain exact boundary-zero elements.
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
local instance residualLiftOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance residualLiftOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
variable [IsAffine U.toScheme]


local notation "β" => normalizedBoundaryChartMap f hL d V c k n o U hU


local notation "Δ" => originalSourceRankDiscrepancy f hL d V c k n o U hU
local notation "βsource" => originalSourceCompatibleBoundaryMap f hL d V c k n o W U hU hUW

/-- Localized surjectivity is precisely residual correction of every raw invariant lift. -/
theorem originalSource_surjective_iff_residual_corrections
    (P : Ideal Tsource) [P.IsPrime] :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Function.Surjective
      (originalSourceLocalizedCompatibleBoundaryMap f hL d V c k n o W U hU hUW P) ↔
      ∀ a : Sinv, ∃ x : Ω, κ x ∉ P ∧ ∃ w : Sinv, β w = 0 ∧
        ∀ m : ℕ, n < m → m ≤ cutoff → ∀ order : ℕ,
          Δ m order (σ x * a) = Δ m order w := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  refine (originalSourceCompatible_surjective_iff_numerators
    f hL d V c k n o W U hU hUW P).trans ?_
  constructor
  · intro h a
    obtain ⟨x, hx, v, hb, hv⟩ := h (β a)
    refine ⟨x, hx, ?_⟩
    apply (originalSource_lift_iff_residual_correction
      f hL d V c k n o W U hU hUW (σ x * a)).mp
    refine ⟨v, (mem_originalSourceCompatibleModule
      f hL d V c k n o W U hU hUW v).mpr hv, ?_⟩
    simpa only [map_mul] using hb
  · intro h t
    obtain ⟨a, ha⟩ := normalizedBoundaryChartMap_surjective f hL d V c k n o U hU
      (show IsAffine U.toScheme from inferInstance) t
    obtain ⟨x, hx, w, hw, hΔ⟩ := h a
    obtain ⟨v, hv, hb⟩ := (originalSource_lift_iff_residual_correction
      f hL d V c k n o W U hU hUW (σ x * a)).mpr ⟨w, hw, hΔ⟩
    refine ⟨x, hx, v, ?_, (mem_originalSourceCompatibleModule
      f hL d V c k n o W U hU hUW v).mp hv⟩
    simpa only [map_mul, ha] using hb

/-- Independent residual corrections for finitely many raw lifts share one original scalar. -/
theorem originalSource_residual_corrections_linear_lift {I : Type} [Finite I]
    (P : Ideal Tsource) [P.IsPrime] (a : I → Sinv)
    (h : ∀ idx, ∃ x : Ω, κ x ∉ P ∧ ∃ w : Sinv, β w = 0 ∧
      ∀ m : ℕ, n < m → m ≤ cutoff → ∀ order : ℕ,
        Δ m order (σ x * a idx) = Δ m order w) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    ∃ x : Ω, κ x ∉ P ∧ ∃ L : (I →₀ Ω) →ₗ[Ω] Csource,
      (βsource).comp L = x • Finsupp.linearCombination Ω (fun idx ↦ β (a idx)) := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  apply OriginalScalarFiniteLinearLifts.exists_linear_lift
    Csource (α).toLinearMap (P.comap κ) (fun idx ↦ β (a idx))
  intro idx
  obtain ⟨x, hx, w, hw, hΔ⟩ := h idx
  obtain ⟨v, hv, hb⟩ := (originalSource_lift_iff_residual_correction
    f hL d V c k n o W U hU hUW (σ x * a idx)).mpr ⟨w, hw, hΔ⟩
  refine ⟨x, hx, ⟨v, hv⟩, ?_⟩
  change β v = β (σ x) * β (a idx)
  simpa only [map_mul] using hb

/-- Residual corrections of a finite spanning family lift the full original localized map. -/
theorem originalSource_surjective_of_spanning_residual_corrections {I : Type} [Finite I]
    (P : Ideal Tsource) [P.IsPrime] (a : I → Sinv)
    (ht : let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
      Submodule.span Ω (Set.range (fun idx ↦ β (a idx))) = ⊤)
    (h : ∀ idx, ∃ x : Ω, κ x ∉ P ∧ ∃ w : Sinv, β w = 0 ∧
      ∀ m : ℕ, n < m → m ≤ cutoff → ∀ order : ℕ,
        Δ m order (σ x * a idx) = Δ m order w) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Function.Surjective
      (originalSourceLocalizedCompatibleBoundaryMap f hL d V c k n o W U hU hUW P) := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  obtain ⟨x, hx, L, hlin⟩ := originalSource_residual_corrections_linear_lift
    f hL d V c k n o W U hU hUW P a h
  exact OriginalScalarGeneratedLocalizedLifts.surjective_of_span Csource (α).toLinearMap
    (originalSubframePrimeDenominators f hL d V c k W P)
    (fun idx ↦ β (a idx)) ⟨x, hx⟩ L hlin ht

end FLT.Mazur.HilbertChart.AffineRestriction
