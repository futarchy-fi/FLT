/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceActualMultiplierIdeal
public import FLT.Mazur.BoundaryCorrectionQuotient

/-!
# The exact original boundary correction quotient

Quotient the original raw source by its compatible submodule and actual
boundary kernel. Its canonical identification with the full boundary cokernel
computes the exact correction ideal, retaining nilpotents and original scalars.
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
local instance correctedQuotientOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance correctedQuotientOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
variable [IsAffine U.toScheme]


local notation "β" => normalizedBoundaryChartMap f hL d V c k n o U hU


local notation "Δ" => originalSourceRankDiscrepancy f hL d V c k n o U hU
local notation "βsource" => originalSourceCompatibleBoundaryMap f hL d V c k n o W U hU hUW

/-- The original numerators correctable by an element of the actual boundary kernel. -/
def originalSourceCorrectableModule :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Submodule Ω Sinv := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  exact BoundaryCorrectionQuotient.correctable Csource (α).toLinearMap

local notation "Ccorr" => originalSourceCorrectableModule f hL d V c k n o W U hU hUW

omit [IsAffine U.toScheme] in
/-- The image of the compatible module is the range of the unchanged boundary map. -/
theorem originalSource_compatible_map_eq_range :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    (Csource).map (α).toLinearMap = LinearMap.range βsource := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  ext t
  constructor
  · rintro ⟨a, ha, ht⟩
    exact ⟨⟨a, ha⟩, ht⟩
  · rintro ⟨a, ht⟩
    exact ⟨a.val, a.property, ht⟩

omit [IsAffine U.toScheme] in
/-- Correctability allows the correction to vary with the original raw numerator. -/
theorem originalSource_mem_correctable_iff (a : Sinv) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    a ∈ Ccorr ↔ ∃ w : Sinv, β w = 0 ∧ a - w ∈ Csource := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  exact BoundaryCorrectionQuotient.mem_correctable_iff Csource (α).toLinearMap a

/-- The actual corrected quotient is the entire compatible boundary cokernel. -/
def originalSourceCorrectedQuotientEquiv :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    (Sinv ⧸ Ccorr) ≃ₗ[Ω] Bsource ⧸ LinearMap.range βsource := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  exact (BoundaryCorrectionQuotient.quotientEquiv Csource (α).toLinearMap
    (normalizedBoundaryChartMap_surjective f hL d V c k n o U hU
      (show IsAffine U.toScheme from inferInstance))).trans
      (Submodule.quotEquivOfEq _ _
        (originalSource_compatible_map_eq_range f hL d V c k n o W U hU hUW))

/-- Exact scalar annihilation permits independent boundary-zero corrections. -/
theorem originalSource_boundary_annihilator_iff_corrections (x : Ω) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    x ∈ Module.annihilator Ω (Bsource ⧸ LinearMap.range βsource) ↔
      ∀ a : Sinv, ∃ w : Sinv, β w = 0 ∧ σ x * a - w ∈ Csource := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  have he : (Csource).map (α).toLinearMap = LinearMap.range βsource :=
    originalSource_compatible_map_eq_range f hL d V c k n o W U hU hUW
  rw [← he]
  exact BoundaryCorrectionQuotient.mem_boundary_annihilator_iff Csource (α).toLinearMap
    (normalizedBoundaryChartMap_surjective f hL d V c k n o U hU
      (show IsAffine U.toScheme from inferInstance)) x

/-- The full cokernel annihilator is computed on original bounded higher ranks, at all orders. -/
theorem originalSource_boundary_annihilator_iff_higher_corrections (x : Ω) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    x ∈ Module.annihilator Ω (Bsource ⧸ LinearMap.range βsource) ↔
      ∀ a : Sinv, ∃ w : Sinv, β w = 0 ∧ ∀ m : ℕ, n < m → m ≤ cutoff →
        ∀ order : ℕ, Δ m order (σ x * a) = Δ m order w := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  refine (originalSource_boundary_annihilator_iff_corrections
    f hL d V c k n o W U hU hUW x).trans ?_
  apply forall_congr'
  intro a
  apply exists_congr
  intro w
  exact and_congr_right fun _ ↦ originalSource_correction_iff_higher_discrepancies
    f hL d V c k n o W U hU hUW (σ x * a) w

end FLT.Mazur.HilbertChart.AffineRestriction
