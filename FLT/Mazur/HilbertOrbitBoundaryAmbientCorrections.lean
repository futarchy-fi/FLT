/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryLinearSystem
public import FLT.Mazur.BoundaryCorrectionAmbientEquations

/-!
# Finite original Hilbert solutions from actual flat ambient equations

Flat ambient corrections on the actual finite atlas reconstruct as finite
families of original simultaneous solutions. A multiplier nonvanishing at a
test prime yields an original nonvanishing lifting scalar and numerator.
Construction of an ambient solution at every boundary point remains separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
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

open BaseLocalizationMap
local notation "ef" => fullRelationSchemeEquivalence f hL d V c k
local notation "n" => fun j : Charts ↦ j.val.size
local notation "o" => fun j : Charts ↦ j.val.label
local notation "U" => fun j : Charts ↦ j.val.domain
local notation "hU" => fun j : Charts ↦ j.val.stable
local notation "F" => MixedFrames.ChartFamily.firstCoefficientMap ef n o U hU
local notation "G" => MixedFrames.ChartFamily.secondCoefficientMap ef n o U hU
local notation "H" => fun j : Charts ↦ normalizedBoundaryChartMap f hL d V c k j.val.size
  j.val.label j.val.domain j.val.stable

attribute [local irreducible] originalChartScalarMap
local notation "α" => originalChartScalarMap f hL d V c k W hW
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "Ac" => chartCoordinateRing f hL d V c k W hW
local notation "Bc" => chartBoundaryCoordinateRing f hL d V c k W hW
local notation "Cc" => mixedCoordinateRing f hL d V c k W hW

attribute [local instance] originalCorrectionChartAlgebra originalCorrectionBoundaryAlgebra
  originalCorrectionMixedAlgebra
local notation "Hb" => originalCorrectionBoundaryHom f hL d V c k W hW
local notation "Fp" => originalCorrectionFirstHom f hL d V c k W hW
local notation "Gq" => originalCorrectionSecondHom f hL d V c k W hW
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))
local notation "u" => lifts f hL d V c k W hW t
local notation "K" => LinearMap.ker (originalCorrectionSystem f hL d V c k W hW t)

/-- Each original solution scalar belongs to the unchanged original lifting ideal. -/
theorem originalCorrectionSolution_scalar_mem (y : K) :
    y.val.1 ∈ originalBoundaryLiftIdeal f hL d V c k W t := by
  exact (originalCorrectionSystem_multiplier_range f hL d V c k W hW t).le ⟨y, rfl⟩

variable (S : Type) [CommRing S]
  [Algebra ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)) S]
  [Module.Flat ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)) S]
  (s : S) (z : ∀ j : finiteCharts f hL d V c k W hW,
    S ⊗[(invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)]
      chartCoordinateRing f hL d V c k W hW j)
  (hb : ∀ j : finiteCharts f hL d V c k W hW,
    (originalCorrectionBoundaryHom f hL d V c k W hW j).toLinearMap.lTensor S (z j) = 0)
  (he : ∀ j l : finiteCharts f hL d V c k W hW,
    (originalCorrectionFirstHom f hL d V c k W hW j l).toLinearMap.lTensor S (z j) -
      (originalCorrectionSecondHom f hL d V c k W hW j l).toLinearMap.lTensor S (z l) =
        s ⊗ₜ[(invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)]
          (originalCorrectionFirstHom f hL d V c k W hW j l (lifts f hL d V c k W hW t j) -
            originalCorrectionSecondHom f hL d V c k W hW j l
              (lifts f hL d V c k W hW t l)))
include hb he
attribute [local irreducible] BoundaryCorrectionIdeal.correctionSystem
  originalCorrectionBoundaryHom originalCorrectionFirstHom originalCorrectionSecondHom

/-- Actual ambient chart corrections reconstruct from finitely many original shared solutions. -/
theorem originalAmbientCorrection_finite :
    ∃ (N : ℕ) (a : Fin N → S) (y : Fin N → K),
      s = ∑ b, algebraMap Ω S (y b).val.1 * a b ∧
      ∀ j : Charts, z j = ∑ b, a b ⊗ₜ[Ω] (y b).val.2 j :=
  BoundaryCorrectionIdeal.ambientCorrection_finite_original
    (R := Ω) (ι := Charts) (A := Ac) (B := Bc) (C := Cc) Hb Fp Gq u S s z hb he

/-- A nonvanishing ambient multiplier produces a scalar in the unchanged original lifting ideal. -/
theorem originalAmbientCorrection_nonvanishing (P : Ideal S) (hs : s ∉ P) :
    ∃ a : Ω, a ∈ originalBoundaryLiftIdeal f hL d V c k W t ∧ algebraMap Ω S a ∉ P := by
  obtain ⟨y, hy⟩ :=
    BoundaryCorrectionIdeal.ambientCorrection_original_nonvanishing Hb Fp Gq u S s z hb he P hs
  refine ⟨y.val.1, ?_, hy⟩
  exact (originalCorrectionSystem_multiplier_range f hL d V c k W hW t).le ⟨y, rfl⟩

/-- Both the nonvanishing scalar and a scaled numerator live in the original invariant ring. -/
theorem originalAmbientCorrection_numerator (P : Ideal S) (hs : s ∉ P) :
    ∃ a b : Ω, algebraMap Ω S a ∉ P ∧
      originalClosedSectionPullback f hL d V c k W b =
        originalClosedSectionPullback f hL d V c k W a * t := by
  obtain ⟨a, ⟨b, hb⟩, ha⟩ :=
    originalAmbientCorrection_nonvanishing f hL d V c k W hW t S s z hb he P hs
  exact ⟨a, b, ha, hb⟩

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
