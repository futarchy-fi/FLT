/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceCorrectionDenominators

/-!
# Patching original boundary-zero corrections

Weighted sums patch residual corrections over the original scalar ring.
Local power corrections on a principal cover construct a full compatible
lift without choosing compatible representatives on pairwise overlaps.
The local residual corrections still have to be supplied by geometry.
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
local instance correctionPatchOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance correctionPatchOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
variable [IsAffine U.toScheme]


local notation "β" => normalizedBoundaryChartMap f hL d V c k n o U hU


local notation "Δ" => originalSourceRankDiscrepancy f hL d V c k n o U hU
local notation "βsource" => originalSourceCompatibleBoundaryMap f hL d V c k n o W U hU hUW

/-- A scalar partition patches actual residual corrections while preserving the boundary. -/
theorem originalSource_patch_residual_corrections {ι : Type} (indices : Finset ι) (a : Sinv)
    (x weights : ι → Ω) (w : ι → Sinv) (hw : ∀ idx ∈ indices, β (w idx) = 0)
    (hΔ : ∀ idx ∈ indices, ∀ m : ℕ, n < m → m ≤ cutoff → ∀ order : ℕ,
      Δ m order (σ (x idx) * a) = Δ m order (w idx))
    (hunit : ∑ idx ∈ indices, weights idx * x idx = 1) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    a - ∑ idx ∈ indices, σ (weights idx) * w idx ∈ Csource ∧
      β (a - ∑ idx ∈ indices, σ (weights idx) * w idx) = β a := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  exact BoundaryCorrectionQuotient.patch_lift Csource (α).toLinearMap indices a x weights w hw
    (fun idx hi ↦ (originalSource_correction_iff_higher_discrepancies
      f hL d V c k n o W U hU hUW (σ (x idx) * a) (w idx)).mpr (hΔ idx hi)) hunit

/-- Power corrections on an original scalar cover construct a full compatible lift. -/
theorem originalSource_lift_of_scalar_correction_cover (a : Sinv) (S : Set Ω)
    (hS : Ideal.span S = ⊤)
    (h : ∀ x ∈ S, ∃ power : ℕ, ∃ w : Sinv, β w = 0 ∧
      ∀ m : ℕ, n < m → m ≤ cutoff → ∀ order : ℕ,
        Δ m order (σ (x ^ power) * a) = Δ m order w) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    ∃ v : Csource, βsource v = β a := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  have hc : a ∈ BoundaryCorrectionQuotient.correctable Csource (α).toLinearMap := by
    apply BoundaryCorrectionQuotient.correctable_of_scalar_cover Csource (α).toLinearMap a S hS
    intro x hx
    obtain ⟨power, w, hw, hΔ⟩ := h x hx
    exact ⟨power, w, hw, (originalSource_correction_iff_higher_discrepancies
      f hL d V c k n o W U hU hUW (σ (x ^ power) * a) w).mpr hΔ⟩
  obtain ⟨w, hw, hv⟩ :=
    (BoundaryCorrectionQuotient.mem_correctable_iff Csource (α).toLinearMap a).mp hc
  refine ⟨⟨a - w, hv⟩, ?_⟩
  change β w = 0 at hw
  change β (a - w) = β a
  rw [map_sub, hw, sub_zero]

/-- Pointwise local corrections on a scalar cover give surjectivity of the unchanged source map. -/
theorem originalSource_surjective_of_scalar_correction_cover (S : Set Ω)
    (hS : Ideal.span S = ⊤)
    (h : ∀ a : Sinv, ∀ x ∈ S, ∃ power : ℕ, ∃ w : Sinv, β w = 0 ∧
      ∀ m : ℕ, n < m → m ≤ cutoff → ∀ order : ℕ,
        Δ m order (σ (x ^ power) * a) = Δ m order w) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Function.Surjective βsource := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  change Function.Surjective βsource
  intro t
  obtain ⟨a, rfl⟩ := normalizedBoundaryChartMap_surjective f hL d V c k n o U hU
    (show IsAffine U.toScheme from inferInstance) t
  exact originalSource_lift_of_scalar_correction_cover f hL d V c k n o W U hU hUW a S hS (h a)

end FLT.Mazur.HilbertChart.AffineRestriction
