/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitMixedResidualSplitting
public import FLT.Mazur.HilbertOrbitMixedBoundaryKernel

/-!
# Residual projection preserves the exact original mixed boundary kernel

Take the product over every independent pair on the fixed Hilbert atlas.
The residual projector multiplies each coordinate by its actual selecting
idempotent, so it preserves the exact boundary ideals, including nilpotents.
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
local instance originalResidualBoundary_sourceSeparated (n : ℕ) (o : Fin n) :
    (source (fst f hL d V c k).left (snd f hL d V c k).left (Fin n) o).IsSeparated :=
  normalizedFrameSource_separated f hL d V c k n o

attribute [local instance] originalMixedResidualAlgebra
local notation "Cr" => originalMixedResidualRing f hL d V c k W hW
local notation "N" => originalMixedBoundaryKernel f hL d V c k W hW
local notation "extR" => originalMixedResidualExtension f hL d V c k W hW
local notation "resR" => originalMixedResidualRestriction f hL d V c k W hW

/-- Extend an entire independent residual family into the original mixed coefficients. -/
def originalResidualFamilyExtension : (∀ j l : Charts, Cr j l) →ₗ[Ω]
    (∀ j l : Charts, Cc j l) :=
  LinearMap.piMap fun j ↦ LinearMap.piMap fun l ↦ extR j l

/-- Restrict every original mixed coordinate to its own actual residual component. -/
def originalResidualFamilyRestriction : (∀ j l : Charts, Cc j l) →ₗ[Ω]
    (∀ j l : Charts, Cr j l) :=
  LinearMap.piMap fun j ↦ LinearMap.piMap fun l ↦ resR j l

/-- The full independent residual family has the constructed original scalar splitting. -/
theorem originalResidualFamily_split :
    (originalResidualFamilyRestriction f hL d V c k W hW).comp
      (originalResidualFamilyExtension f hL d V c k W hW) = LinearMap.id := by
  ext x j l
  exact LinearMap.congr_fun (originalMixedResidual_split f hL d V c k W hW j l) (x j l)

/-- Each actual residual projector is multiplication by its selecting idempotent. -/
theorem originalMixedResidual_project (j l : Charts) (x : Cc j l) :
    extR j l (resR j l x) = x * extR j l 1 := by
  let eqv := (MixedFrames.mixedResidualBranchSectionsIso ef j.val.label l.val.label
    (MixedFrames.mixedChartOpen j.val.label l.val.label j.val.domain l.val.domain).ι
    ).commRingCatIsoToRingEquiv
  change ResidualProductExtension.extension eqv (ResidualProductExtension.projection eqv x) =
    x * ResidualProductExtension.extension eqv 1
  rw [ResidualProductExtension.mul_extension, mul_one]

/-- Projection preserves the exact original boundary kernel, without radicalization. -/
theorem originalResidualFamily_preserves_boundary (x : ∀ j l : Charts, Cc j l)
    (hx : x ∈ N) :
    originalResidualFamilyExtension f hL d V c k W hW
      (originalResidualFamilyRestriction f hL d V c k W hW x) ∈ N := by
  rw [mem_originalMixedBoundaryKernel_iff] at hx ⊢
  intro j l
  change extR j l (resR j l (x j l)) ∈ _
  rw [originalMixedResidual_project]
  exact Ideal.mul_mem_right _ _ (hx j l)

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
