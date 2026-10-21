/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageBoundaryScalarAnnihilation
public import FLT.Mazur.SchemeScalarIntegralBadCover

/-!
# Geometric support of the actual boundary correction class

The full boundary kernel cuts out the closure of the original scalar image
of the boundary. Outside this closure one original scalar vanishes on the
entire unreduced boundary and corrects every whole-core cochain. No finite
or closed original scalar projection is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsAffine A] (J : A.IdealSheafData)
local notation "σ" => Subring.subtype (compatibleFunctions p q)

/-- The scalar kernel is the contraction of the original full affine boundary ideal. -/
theorem originalBoundaryScalarKernel_eq_comap :
    originalBoundaryScalarKernel (p := p) (q := q) J =
      Ideal.comap σ (J.ideal ⟨⊤, isAffineOpen_top A⟩) := by
  rw [originalBoundaryScalarKernel, ← RingHom.comap_ker,
    J.ker_subschemeι_app ⟨⊤, isAffineOpen_top A⟩]

/-- The exact kernel defines the closure of the whole original boundary image. -/
theorem originalBoundaryScalarKernel_zeroLocus :
    PrimeSpectrum.zeroLocus
        (originalBoundaryScalarKernel (p := p) (q := q) J : Set (compatibleFunctions p q)) =
      closure (scalarMorphism σ '' (J.support : Set A)) := by
  let _ : IsAffine J.subscheme := isAffine_of_isAffineHom J.subschemeι
  have hj : Set.range J.subschemeι = (J.support.compl : Set A)ᶜ := by
    simpa only [TopologicalSpace.Closeds.coe_compl, compl_compl] using J.range_subschemeι
  have he := scalar_badImage_eq_badCover_range σ J.support.compl J.subschemeι hj
  simp only [TopologicalSpace.Closeds.coe_compl, compl_compl] at he
  rw [he,
    scalarMorphism_range_eq_comap, PrimeSpectrum.closure_range_comap]
  rfl

/-- A prime off the boundary image closure has an exact full-boundary annihilator. -/
theorem exists_originalBoundaryScalarKernel_away
    (x : PrimeSpectrum (compatibleFunctions p q))
    (hx : x ∉ closure (scalarMorphism σ '' (J.support : Set A))) :
    ∃ s : compatibleFunctions p q, s ∉ x.asIdeal ∧
      s ∈ originalBoundaryScalarKernel (p := p) (q := q) J ∧
      A.basicOpen s.val ≤ J.support.compl := by
  let _ : IsAffine J.subscheme := isAffine_of_isAffineHom J.subschemeι
  have hj : Set.range J.subschemeι = (J.support.compl : Set A)ᶜ := by
    simpa only [TopologicalSpace.Closeds.coe_compl, compl_compl] using J.range_subschemeι
  apply exists_scalar_killing_badCover σ J.support.compl J.subschemeι hj x
  change x ∉ closure (scalarMorphism σ '' (J.support.compl : Set A)ᶜ)
  simpa only [TopologicalSpace.Closeds.coe_compl, compl_compl] using hx

variable [IsSeparated p] [Etale p] [QuasiCompact p] [Etale q]
  [IsLocallyNoetherian A] [LocallyQuasiFinite p]
  (e : CategoryTheory.EquivalenceRelation p q)
local instance boundaryGeometryOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance boundaryGeometryOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance boundaryGeometryOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) {ι : Type*} (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
  (v : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j))
attribute [local irreducible] rankStageCoreCorrectionIdeal

/-- Actual correction support lies in the closure of the whole original boundary image. -/
theorem rankStageCoreCorrection_support_subset_boundary_image :
    PrimeSpectrum.zeroLocus
        (rankStageCoreCorrectionIdeal e n c hc J v : Set (compatibleFunctions p q)) ⊆
      closure (scalarMorphism σ '' (J.support : Set A)) := by
  rw [← originalBoundaryScalarKernel_zeroLocus]
  exact rankStageCoreCorrection_support_subset_boundary e n c hc J v

/-- A geometric original neighborhood supplies an actual correction scalar. -/
theorem exists_rankStageCoreCorrectionScalar_off_boundary
    (x : PrimeSpectrum (compatibleFunctions p q))
    (hx : x ∉ closure (scalarMorphism σ '' (J.support : Set A))) :
    ∃ s : compatibleFunctions p q, s ∉ x.asIdeal ∧
      s ∈ rankStageCoreCorrectionIdeal e n c hc J v ∧ A.basicOpen s.val ≤ J.support.compl := by
  obtain ⟨s, hs, hJ, hO⟩ := exists_originalBoundaryScalarKernel_away J x hx
  exact ⟨s, hs, originalBoundaryScalarKernel_le_correctionIdeal e n c hc J v hJ, hO⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
