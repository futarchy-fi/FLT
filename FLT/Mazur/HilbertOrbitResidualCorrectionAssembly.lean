/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitResidualCorrectionCoordinates

/-!
# Assemble embedding and residual corrections on the original atlas

A boundary-zero family solving every embedding equation leaves a supported
residual error. A second boundary-zero family representing that residual error
then gives an exact full correction by addition. All families and coefficients
remain on the unchanged original atlas.
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

attribute [local irreducible] BoundaryCorrectionIdeal.mixedDiscrepancy
  BoundaryCorrectionIdeal.boundaryCoordinates originalCorrectionBoundaryHom
  originalCorrectionFirstHom originalCorrectionSecondHom
  originalResidualFamilyExtension originalResidualFamilyRestriction
local notation "Kr" => originalResidualCorrectionModule f hL d V c k W hW
local notation "bdy" => BoundaryCorrectionIdeal.boundaryCoordinates Hb

/-- An embedding correction and a realized residual correction assemble into a full witness. -/
theorem originalResidualCorrection_assemble (x : ∀ j l : Charts, Cc j l)
    (u : ∀ j : Charts, Ac j) (hu : bdy u = 0)
    (hg : ∀ (j l : Charts) (ι : Fin l.val.size ↪ Fin j.val.size),
      originalMixedEmbeddingCoefficient f hL d V c k W hW j l ι ((x - δ u) j l) = 0)
    (hr : resF (x - δ u) ∈ Kr) :
    ∃ w : ∀ j : Charts, Ac j, bdy w = 0 ∧ δ w = x := by
  obtain ⟨v, hv, hrv, hgv⟩ :=
    (mem_originalResidualCorrection_iff f hL d V c k W hW _).mp hr
  have he : δ v = extF (resF (x - δ u)) :=
    (originalResidualFamily_equation_iff f hL d V c k W hW _ _).mpr ⟨hrv, hgv⟩
  have hs : x - δ u = extF (resF (x - δ u)) :=
    (originalResidualFamily_equation_iff f hL d V c k W hW _ _).mpr ⟨rfl, hg⟩
  refine ⟨u + v, ?_, ?_⟩
  · exact (map_add bdy u v).trans ((congrArg₂ (· + ·) hu hv).trans (add_zero 0))
  · calc
      δ (u + v) = δ u + δ v := map_add δ u v
      _ = δ u + (x - δ u) := congrArg (δ u + ·) (he.trans hs.symm)
      _ = x := (add_comm _ _).trans (sub_add_cancel _ _)

/-- Full correction membership is a graph stage followed by exact residual correction membership. -/
theorem originalMixedCorrection_mem_iff_residual_stages (x : ∀ j l : Charts, Cc j l) :
    x ∈ K ↔ ∃ u : ∀ j : Charts, Ac j, bdy u = 0 ∧
      (∀ (j l : Charts) (ι : Fin l.val.size ↪ Fin j.val.size),
        originalMixedEmbeddingCoefficient f hL d V c k W hW j l ι ((x - δ u) j l) = 0) ∧
      resF (x - δ u) ∈ Kr := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_, ?_⟩
    · intro j l ι
      simp only [sub_self, Pi.zero_apply, map_zero]
    · simp only [sub_self, map_zero, Submodule.zero_mem]
  · rintro ⟨u, hu, hg, hr⟩
    obtain ⟨w, hw, hx⟩ := originalResidualCorrection_assemble f hL d V c k W hW x u hu hg hr
    exact ⟨w, hw, hx⟩

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
