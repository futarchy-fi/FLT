/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitResidualBoundarySplitting
public import FLT.Mazur.HilbertOrbitResidualEmbeddingEquations

/-!
# The exact original correction image in residual coordinates

Residual corrections are pulled back from the original correction image.
Their witnesses still solve all original boundary equations and every
independent embedding equation. No arbitrary lifts are declared compatible.
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
attribute [local instance] originalMixedResidualAlgebra
local notation "Cr" => originalMixedResidualRing f hL d V c k W hW
local notation "N" => originalMixedBoundaryKernel f hL d V c k W hW
local notation "extR" => originalMixedResidualExtension f hL d V c k W hW
local notation "resR" => originalMixedResidualRestriction f hL d V c k W hW

local notation "extF" => originalResidualFamilyExtension f hL d V c k W hW
local notation "resF" => originalResidualFamilyRestriction f hL d V c k W hW

attribute [local instance] originalCorrectionChartAlgebra originalCorrectionBoundaryAlgebra
local notation "Ac" => chartCoordinateRing f hL d V c k W hW
local notation "Hb" => originalCorrectionBoundaryHom f hL d V c k W hW
local notation "Fp" => originalCorrectionFirstHom f hL d V c k W hW
local notation "Gq" => originalCorrectionSecondHom f hL d V c k W hW
local notation "K" => originalBoundaryMixedCorrectionImage f hL d V c k W hW
local notation "δ" => BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq

/-- Residual coordinates realized by actual full boundary-zero original corrections. -/
def originalResidualCorrectionModule : Submodule Ω (∀ j l : Charts, Cr j l) :=
  (K).comap extF

/-- Every realized residual correction satisfies the exact original boundary equations. -/
theorem originalResidualCorrection_le_boundary :
    originalResidualCorrectionModule f hL d V c k W hW ≤
      originalResidualBoundaryModule f hL d V c k W hW :=
  Submodule.comap_mono (originalMixedCorrectionImage_le_boundary f hL d V c k W hW)

/-- Exact correction membership retains all independent original embedding equations. -/
theorem mem_originalResidualCorrection_iff (a : ∀ j l : Charts, Cr j l) :
    a ∈ originalResidualCorrectionModule f hL d V c k W hW ↔
      ∃ u : ∀ j : Charts, Ac j,
        BoundaryCorrectionIdeal.boundaryCoordinates Hb u = 0 ∧
        resF (δ u) = a ∧
        ∀ (j l : Charts) (ι : Fin l.val.size ↪ Fin j.val.size),
          originalMixedEmbeddingCoefficient f hL d V c k W hW j l ι (δ u j l) = 0 := by
  change (∃ u, u ∈ LinearMap.ker (BoundaryCorrectionIdeal.boundaryCoordinates Hb) ∧
    δ u = extF a) ↔ _
  simp only [LinearMap.mem_ker, originalResidualFamily_equation_iff]

/-- Extending realized residual corrections gives exactly the supported original corrections. -/
theorem originalResidualCorrection_image :
    (originalResidualCorrectionModule f hL d V c k W hW).map extF =
      K ⊓ LinearMap.range extF := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨ha, ⟨a, rfl⟩⟩
  · rintro x ⟨hx, a, rfl⟩
    exact ⟨a, hx, rfl⟩

/-- A residual boundary coefficient is removable precisely by an actual compatible correction. -/
theorem originalResidualBoundary_class_zero_iff
    (a : originalResidualBoundaryModule f hL d V c k W hW) :
    (K).mkQ (extF a.val) = 0 ↔
      a.val ∈ originalResidualCorrectionModule f hL d V c k W hW :=
  Submodule.Quotient.mk_eq_zero K

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
