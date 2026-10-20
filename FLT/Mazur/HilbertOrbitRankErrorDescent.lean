/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitAdicReducedLifts
public import FLT.Mazur.AdicLinearRankReduction

/-!
# Full old-atlas boundary descent from cofinal rank errors

The error ideal belongs to the complete original boundary-and-mixed equation
ring. Entire scalar-fiber support gives one cofinal bound converting these
errors to actual original scalar reductions. Original scalar finiteness and
the full approximation hypotheses remain explicit geometric obligations.
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

attribute [local irreducible] originalChartScalarMap
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "Ac" => chartCoordinateRing f hL d V c k W hW
local notation "Bc" => chartBoundaryCoordinateRing f hL d V c k W hW
local notation "Cc" => mixedCoordinateRing f hL d V c k W hW

local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "D" => (invariantSheaf ec).obj.obj (op Wc)
local notation "ρ" => originalClosedSectionPullback f hL d V c k W

attribute [local instance] originalBoundarySectionAlgebra originalCorrectionBoundaryAlgebra
  originalCorrectionChartAlgebra originalCorrectionMixedAlgebra
attribute [local irreducible] originalBoundaryCoefficientLinearMap
  BoundaryCorrectionIdeal.originalCorrectionOperator
  originalCorrectionBoundaryHom originalCorrectionFirstHom originalCorrectionSecondHom
local notation "Hb" => originalCorrectionBoundaryHom f hL d V c k W hW
local notation "Fp" => originalCorrectionFirstHom f hL d V c k W hW
local notation "Gq" => originalCorrectionSecondHom f hL d V c k W hW
local notation "β" => originalBoundaryCoefficientLinearMap f hL d V c k W hW
local notation "F₀" => BoundaryCorrectionIdeal.originalCorrectionOperator Hb Fp Gq 0

local notation "Target" => ((∀ j : Charts, Bc j) × ∀ j l : Charts, Cc j l)
local notation "Q" => LinearMap.range F₀

/-- Full old-atlas rank errors give a numerator over the unchanged original scalars. -/
theorem originalBoundary_exists_rank_error_numerator (hΩ : IsNoetherianRing Ω)
    (hfinite : Module.Finite Ω (Target ⧸ Q)) (J P : Ideal Ω)
    (hJP : J ≤ P) (hP : P ≠ ⊤) (K : Ideal Target) (hK : K.FG)
    (hsupport : PrimeSpectrum.zeroLocus (J.map (algebraMap Ω Target) : Set Target) ⊆
      PrimeSpectrum.zeroLocus (K : Set Target)) (t : D)
    (h : ∀ order : ℕ, ∃ v : ∀ j : Charts, Ac j, (β t, 0) - F₀ v ∈ K ^ (order + 1)) :
    ∃ s : Ω, s ∉ P ∧ 1 - s ∈ J ∧ ∃ a : Ω, ρ a = s • t := by
  apply originalBoundary_exists_reduced_numerator f hL d V c k W hW hΩ hfinite J P hJP hP t
  exact AdicLinearImageDescent.reduced_solutions_of_rank_errors F₀ J K hK hsupport (β t, 0) h

/-- The complete original operator has an unscaled invariant lift over local original scalars. -/
theorem originalBoundary_exists_rank_error_lift (hΩ : IsNoetherianRing Ω)
    (hlocal : IsLocalRing Ω) (hfinite : Module.Finite Ω (Target ⧸ Q))
    (J : Ideal Ω) (hJ : J ≠ ⊤) (K : Ideal Target) (hK : K.FG)
    (hsupport : PrimeSpectrum.zeroLocus (J.map (algebraMap Ω Target) : Set Target) ⊆
      PrimeSpectrum.zeroLocus (K : Set Target)) (t : D)
    (h : ∀ order : ℕ, ∃ v : ∀ j : Charts, Ac j, (β t, 0) - F₀ v ∈ K ^ (order + 1)) :
    ∃ a : Ω, ρ a = t := by
  apply originalBoundary_exists_reduced_lift f hL d V c k W hW hΩ hlocal hfinite J hJ t
  exact AdicLinearImageDescent.reduced_solutions_of_rank_errors F₀ J K hK hsupport (β t, 0) h

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
