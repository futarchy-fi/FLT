/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryLinearSystem
public import FLT.Mazur.BoundaryCorrectionFiniteReduction

/-!
# Original Hilbert lifts constructed from finite error reduction matrices

A fixed finite frame and its full-equation reduction matrix construct original
nonvanishing scalars and scaled invariant numerators over any flat ambient
algebra of the original scalar ring. Neither a Noetherian hypothesis nor
all-order approximations are inputs. The finite geometric reduction data
must still be constructed at each boundary point.
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

local notation "D" => originalCorrectionSystem f hL d V c k W hW t
local notation "Pair" => FiniteErrorLinearLifting.tensorPair (R := Ω) (M := ∀ j : Charts, Ac j) S

attribute [local irreducible] FiniteErrorLinearLifting.tensorPair
  BoundaryCorrectionIdeal.correctionSystem
  originalCorrectionBoundaryHom originalCorrectionFirstHom originalCorrectionSecondHom


/-- Finite full-equation reductions give an original nonvanishing lifting scalar. -/
theorem originalFiniteReduction_nonvanishing
    (J : Ideal S) {η : Type} [Fintype η]
    (ε : η → S ⊗[Ω] ((∀ j : Charts, Bc j) × ∀ j l : Charts, Cc j l))
    (v : η → S ⊗[Ω] (∀ j : Charts, Ac j)) (mat : η → η → S)
    (hmat : ∀ j l, mat j l ∈ J)
    (hε : ∀ j, ε j - (D).baseChange S (Pair (0, v j)) = ∑ l, mat j l • ε l)
    (z₀ : S ⊗[Ω] (∀ j : Charts, Ac j)) (b : η → S)
    (h₀ : (D).baseChange S (Pair (1, z₀)) = ∑ j, b j • ε j)
    (P : Ideal S) (hJP : J ≤ P) (hP : P ≠ ⊤) :
    ∃ a : Ω, a ∈ originalBoundaryLiftIdeal f hL d V c k W t ∧ algebraMap Ω S a ∉ P := by
  obtain ⟨y, hy⟩ := BoundaryCorrectionIdeal.finiteReduction_original
    Hb Fp Gq u S J ε v mat hmat hε z₀ b h₀ P hJP hP
  refine ⟨y.val.1, ?_, hy⟩
  exact (originalCorrectionSystem_multiplier_range f hL d V c k W hW t).le ⟨y, rfl⟩

/-- The constructed original scalar has an actual original invariant scaled numerator. -/
theorem originalFiniteReduction_numerator
    (J : Ideal S) {η : Type} [Fintype η]
    (ε : η → S ⊗[Ω] ((∀ j : Charts, Bc j) × ∀ j l : Charts, Cc j l))
    (v : η → S ⊗[Ω] (∀ j : Charts, Ac j)) (mat : η → η → S)
    (hmat : ∀ j l, mat j l ∈ J)
    (hε : ∀ j, ε j - (D).baseChange S (Pair (0, v j)) = ∑ l, mat j l • ε l)
    (z₀ : S ⊗[Ω] (∀ j : Charts, Ac j)) (b : η → S)
    (h₀ : (D).baseChange S (Pair (1, z₀)) = ∑ j, b j • ε j)
    (P : Ideal S) (hJP : J ≤ P) (hP : P ≠ ⊤) :
    ∃ a b : Ω, algebraMap Ω S a ∉ P ∧
      originalClosedSectionPullback f hL d V c k W b =
        originalClosedSectionPullback f hL d V c k W a * t := by
  obtain ⟨a, ⟨w, hw⟩, ha⟩ := originalFiniteReduction_nonvanishing
    f hL d V c k W hW t S J ε v mat hmat hε z₀ b h₀ P hJP hP
  exact ⟨a, w, ha, hw⟩

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
