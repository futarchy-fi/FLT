/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryLinearSystem
public import FLT.Mazur.BoundaryCorrectionAdicAmbient

/-!
# Original Hilbert lifts from uniformly finite ambient errors

The full original correction system is approximated over a flat Noetherian
algebra of the ORIGINAL invariant scalar ring. A single finite error module
at every order constructs an actual original nonvanishing lifting scalar.
The existence of these full approximations is a separate geometric task;
empty complete residual stages do not supply them.
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

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "Charts" => finiteCharts f hL d V c k W hW

attribute [local irreducible] originalChartScalarMap
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

variable (S : Type) [CommRing S]
  [Algebra ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)) S]
  [Module.Flat ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)) S]
  [IsNoetherianRing S]

local notation "D" => originalCorrectionSystem f hL d V c k W hW t
local notation "Pair" => FiniteErrorLinearLifting.tensorPair (R := Ω) (M := ∀ j : Charts, Ac j) S

attribute [local irreducible] BoundaryCorrectionIdeal.correctionSystem
  originalCorrectionBoundaryHom originalCorrectionFirstHom originalCorrectionSecondHom

/-- Uniform finite control of every full ambient error gives an original lifting scalar. -/
theorem originalFiniteErrorCorrection_nonvanishing
    (J : Ideal S) (E : Submodule S (S ⊗[Ω] ((∀ j : Charts, Bc j) × ∀ j l : Charts, Cc j l)))
    (hE : E.FG)
    (h : ∀ n : ℕ, ∃ z : S ⊗[Ω] (∀ j : Charts, Ac j),
      (D).baseChange S (Pair (1, z)) ∈ J ^ n • E)
    (P : Ideal S) (hJP : J ≤ P) (hP : P ≠ ⊤) :
    ∃ a : Ω, a ∈ originalBoundaryLiftIdeal f hL d V c k W t ∧ algebraMap Ω S a ∉ P := by
  obtain ⟨y, hy⟩ := BoundaryCorrectionIdeal.adicAmbientCorrection_original
    Hb Fp Gq u S J E hE h P hJP hP
  refine ⟨y.val.1, ?_, hy⟩
  exact (originalCorrectionSystem_multiplier_range f hL d V c k W hW t).le ⟨y, rfl⟩

/-- The scalar comes with an actual numerator in the original invariant ring. -/
theorem originalFiniteErrorCorrection_numerator
    (J : Ideal S) (E : Submodule S (S ⊗[Ω] ((∀ j : Charts, Bc j) × ∀ j l : Charts, Cc j l)))
    (hE : E.FG)
    (h : ∀ n : ℕ, ∃ z : S ⊗[Ω] (∀ j : Charts, Ac j),
      (D).baseChange S (Pair (1, z)) ∈ J ^ n • E)
    (P : Ideal S) (hJP : J ≤ P) (hP : P ≠ ⊤) :
    ∃ a b : Ω, algebraMap Ω S a ∉ P ∧
      originalClosedSectionPullback f hL d V c k W b =
        originalClosedSectionPullback f hL d V c k W a * t := by
  obtain ⟨a, ⟨b, hb⟩, ha⟩ :=
    originalFiniteErrorCorrection_nonvanishing f hL d V c k W hW t S J E hE h P hJP hP
  exact ⟨a, b, ha, hb⟩

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
