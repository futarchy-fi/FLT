/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryObstructionKernel
public import FLT.Mazur.AdicLinearImageDescent

/-!
# Full original boundary descent from adic equations on the old atlas

Both the boundary equations and every mixed equation are approximated on
the unchanged atlas. Finite original correction cokernel then gives an
actual invariant numerator. Rank-stage towers alone do not provide these
original approximations or the stated finiteness hypotheses.
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

/-- All original equations, solved to every order, descend to a full invariant numerator. -/
theorem originalBoundary_exists_adic_numerator (hΩ : IsNoetherianRing Ω)
    (hfinite : Module.Finite Ω (Target ⧸ Q)) (J P : Ideal Ω)
    (hJP : J ≤ P) (hP : P ≠ ⊤) (t : D)
    (h : ∀ n₀ : ℕ, ∃ v : ∀ j : Charts, Ac j,
      (β t, 0) - F₀ v ∈ J ^ (n₀ + 1) • (⊤ : Submodule Ω Target)) :
    ∃ s : Ω, s ∉ P ∧ 1 - s ∈ J ∧ ∃ a : Ω, ρ a = s • t := by
  let _ := hΩ
  let _ := hfinite
  obtain ⟨s, hs, hj, v, hv⟩ :=
    AdicLinearImageDescent.exists_scaled_solution F₀ J P hJP hP (β t, 0) h
  refine ⟨s, hs, hj, ?_⟩
  apply (originalBoundaryObstruction_eq_zero_iff_lift f hL d V c k W hW (s • t)).mp
  change (Q).mkQ (β (s • t), 0) = 0
  apply (Submodule.Quotient.mk_eq_zero Q).mpr
  refine ⟨v, ?_⟩
  simpa only [map_smul, Prod.smul_mk, smul_zero] using hv

/-- Local original scalars give an exact original invariant with the unchanged boundary. -/
theorem originalBoundary_exists_adic_lift (hΩ : IsNoetherianRing Ω)
    (hlocal : IsLocalRing Ω) (hfinite : Module.Finite Ω (Target ⧸ Q))
    (J : Ideal Ω) (hJ : J ≠ ⊤) (t : D)
    (h : ∀ n₀ : ℕ, ∃ v : ∀ j : Charts, Ac j,
      (β t, 0) - F₀ v ∈ J ^ (n₀ + 1) • (⊤ : Submodule Ω Target)) :
    ∃ a : Ω, ρ a = t := by
  let _ := hΩ
  let _ := hlocal
  let _ := hfinite
  obtain ⟨v, hv⟩ := AdicLinearImageDescent.exists_solution_of_local F₀ J hJ (β t, 0) h
  apply (originalBoundaryObstruction_eq_zero_iff_lift f hL d V c k W hW t).mp
  change (Q).mkQ (β t, 0) = 0
  exact (Submodule.Quotient.mk_eq_zero Q).mpr ⟨v, hv⟩

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
