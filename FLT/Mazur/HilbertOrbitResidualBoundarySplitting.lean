/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitResidualBoundaryProjection
public import FLT.Mazur.SplitSubmoduleInternalReduction

/-!
# Split the residual part inside the original mixed boundary kernel

The restricted splitting is constructed from preservation of the actual
boundary ideals. Its reduction statement is internal to that kernel, over
any scalar ideal. The full boundary correction quotient is still distinct.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency true
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

attribute [local irreducible] originalMixedBoundaryKernel
  originalResidualFamilyExtension originalResidualFamilyRestriction
attribute [local instance] originalCorrectionMixedAlgebra
attribute [local instance] originalMixedResidualAlgebra
local notation "Cr" => originalMixedResidualRing f hL d V c k W hW
local notation "N" => originalMixedBoundaryKernel f hL d V c k W hW
local notation "extR" => originalMixedResidualExtension f hL d V c k W hW
local notation "resR" => originalMixedResidualRestriction f hL d V c k W hW

local notation "extF" => originalResidualFamilyExtension f hL d V c k W hW
local notation "resF" => originalResidualFamilyRestriction f hL d V c k W hW

/-- Exact residual coordinates whose extension vanishes on the original mixed boundary. -/
def originalResidualBoundaryModule : Submodule Ω (∀ j l : Charts, Cr j l) :=
  (N).comap extF

/-- Extend residual boundary coefficients into the exact original mixed boundary module. -/
def originalResidualBoundaryExtension :
    originalResidualBoundaryModule f hL d V c k W hW →ₗ[Ω] N :=
  SplitSubmoduleReduction.internalExtension extF N

/-- Restriction on the original boundary is constructed using its ideal stability. -/
def originalResidualBoundaryRestriction :
    N →ₗ[Ω] originalResidualBoundaryModule f hL d V c k W hW :=
  SplitSubmoduleReduction.internalRestriction extF resF N
    (originalResidualFamily_preserves_boundary f hL d V c k W hW)

/-- The residual boundary coefficients are split inside the original boundary itself. -/
theorem originalResidualBoundary_split :
    (originalResidualBoundaryRestriction f hL d V c k W hW).comp
      (originalResidualBoundaryExtension f hL d V c k W hW) = LinearMap.id :=
  SplitSubmoduleReduction.internal_split extF resF
    (originalResidualFamily_split f hL d V c k W hW) N
    (originalResidualFamily_preserves_boundary f hL d V c k W hW)

/-- Internal boundary ideal multiples do not hide any supported boundary coefficient. -/
theorem originalResidualBoundary_internal_absorption (J : Ideal Ω) :
    LinearMap.range (originalResidualBoundaryExtension f hL d V c k W hW) ⊓
        J • (⊤ : Submodule Ω N) =
      J • LinearMap.range (originalResidualBoundaryExtension f hL d V c k W hW) :=
  SplitSubmoduleReduction.range_inf_smul_top _ _
    (originalResidualBoundary_split f hL d V c k W hW) J

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
