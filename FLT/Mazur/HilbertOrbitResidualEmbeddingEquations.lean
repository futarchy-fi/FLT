/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitResidualBoundaryProjection

/-!
# Exact residual equations retain every original embedding equation

An equation in the original mixed ring is equivalent to its residual equation
and the zero equations on all independently labeled embedding branches.
The product formulation keeps the original atlas and arbitrary frame sizes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relativeFppfSheaf AmpleLineBundle
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
attribute [local irreducible] relation fst snd equivalence
  EquivalenceRelationNormalizedFrames.source
namespace OrbitBoundaryAtlas.FiniteAtlas
attribute [local irreducible] finiteCharts lifts obstruction
  scalarFamily normalizedBoundaryChartMap normalizedOrbitBoundaryCoefficient
local notation "e" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "Charts" => finiteCharts f hL d V c k W hW

local notation "ef" => fullRelationSchemeEquivalence f hL d V c k
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "Cc" => mixedCoordinateRing f hL d V c k W hW

attribute [local instance] originalCorrectionMixedAlgebra
local instance originalResidualEquation_sourceSeparated (n : ℕ) (o : Fin n) :
    (source (fst f hL d V c k).left (snd f hL d V c k).left (Fin n) o).IsSeparated :=
  normalizedFrameSource_separated f hL d V c k n o

attribute [local instance] originalMixedResidualAlgebra
local notation "Cr" => originalMixedResidualRing f hL d V c k W hW
local notation "N" => originalMixedBoundaryKernel f hL d V c k W hW
local notation "extR" => originalMixedResidualExtension f hL d V c k W hW
local notation "resR" => originalMixedResidualRestriction f hL d V c k W hW

/-- Test a full original mixed coefficient on one individually labeled embedding branch. -/
def originalMixedEmbeddingCoefficient (j l : Charts) (ι : Fin l.val.size ↪ Fin j.val.size) :
    Cc j l →+* Γ((MixedFrames.mixedEmbeddingTestOpen ef j.val.label l.val.label
      (MixedFrames.mixedChartOpen j.val.label l.val.label j.val.domain l.val.domain).ι
      ι).toScheme, ⊤) :=
  (MixedFrames.mixedEmbeddingTestOpen ef j.val.label l.val.label
    (MixedFrames.mixedChartOpen j.val.label l.val.label j.val.domain l.val.domain).ι ι).ι.appTop.hom

/-- Full equality to an extended residual coefficient retains every original graph equation. -/
theorem originalMixedResidual_equation_iff (j l : Charts) (x : Cc j l) (a : Cr j l) :
    x = extR j l a ↔ resR j l x = a ∧
      ∀ ι : Fin l.val.size ↪ Fin j.val.size,
        originalMixedEmbeddingCoefficient f hL d V c k W hW j l ι x = 0 := by
  let z := (MixedFrames.mixedChartOpen j.val.label l.val.label j.val.domain l.val.domain).ι
  let eqv := (MixedFrames.mixedResidualBranchSectionsIso ef j.val.label l.val.label z
    ).commRingCatIsoToRingEquiv
  constructor
  · rintro rfl
    refine ⟨LinearMap.congr_fun (originalMixedResidual_split f hL d V c k W hW j l) a, ?_⟩
    intro ι
    exact MixedFrames.mixedResidualSectionExtension_embedding ef j.val.label l.val.label z a ι
  · rintro ⟨hr, hg⟩
    have hzero : ∀ ι, eqv x (some ι) = 0 := by
      intro ι
      exact (MixedFrames.mixedResidualBranchSectionsIso_apply
        ef j.val.label l.val.label z x (some ι)).trans (hg ι)
    have h := ResidualProductExtension.extension_projection eqv x hzero
    change ResidualProductExtension.projection eqv x = a at hr
    rw [hr] at h
    exact h.symm

/-- Simultaneous equations are exactly the residual family and every embedding test. -/
theorem originalResidualFamily_equation_iff (x : ∀ j l : Charts, Cc j l)
    (a : ∀ j l : Charts, Cr j l) :
    x = originalResidualFamilyExtension f hL d V c k W hW a ↔
      originalResidualFamilyRestriction f hL d V c k W hW x = a ∧
      ∀ (j l : Charts) (ι : Fin l.val.size ↪ Fin j.val.size),
        originalMixedEmbeddingCoefficient f hL d V c k W hW j l ι (x j l) = 0 := by
  constructor
  · intro hx
    have h j l := (originalMixedResidual_equation_iff f hL d V c k W hW j l
      (x j l) (a j l)).mp (congrFun (congrFun hx j) l)
    exact ⟨funext fun j ↦ funext fun l ↦ (h j l).1, fun j l ↦ (h j l).2⟩
  · rintro ⟨hr, hg⟩
    funext j l
    exact (originalMixedResidual_equation_iff f hL d V c k W hW j l _ _).mpr
      ⟨congrFun (congrFun hr j) l, hg j l⟩

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
