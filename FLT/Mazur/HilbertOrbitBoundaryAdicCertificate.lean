/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryFiniteErrors
public import FLT.Mazur.BoundaryCorrectionAdicCertificate
public import FLT.Mazur.HilbertBoundaryCertifiedAlgebra

/-!
# Original boundary certificates from finite ambient errors

An ambient source test preserving the ORIGINAL boundary scalar map and killing
the approximation ideal turns the finite reconstructed congruence into an
actual original closed-source certificate. This is a construction from explicit
approximation data; the general existence of that data is not asserted.
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

local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "T" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)

attribute [local irreducible] BoundaryCorrectionIdeal.correctionSystem
  originalCorrectionBoundaryHom originalCorrectionFirstHom originalCorrectionSecondHom

/-- Finite original correction coefficients certify the unchanged original closed source. -/
theorem originalFiniteErrorCorrection_certified
    (J : Ideal S) (E : Submodule S (S ⊗[Ω] ((∀ j : Charts, Bc j) × ∀ j l : Charts, Cc j l)))
    (hE : E.FG)
    (h : ∀ n : ℕ, ∃ z : S ⊗[Ω] (∀ j : Charts, Ac j),
      (D).baseChange S (Pair (1, z)) ∈ J ^ n • E)
    (ρ : S →+* T) (hρ : ρ.comp (algebraMap Ω S) = κ) (hJ : J ≤ RingHom.ker ρ) :
    t ∈ originalBoundaryCertifiedSections f hL d V c k W := by
  have ht := BoundaryCorrectionIdeal.adicAmbientCorrection_map_eq_top
    Hb Fp Gq u S J E hE h ρ hJ
  have hI := (BoundaryCorrectionIdeal.range_correctionMultiplier Hb Fp Gq u).symm.trans
    (originalCorrectionSystem_multiplier_range f hL d V c k W hW t)
  rw [hI, hρ] at ht
  exact ht

/-- These actual approximation data construct the original finite coefficient certificate. -/
theorem originalFiniteErrorCorrection_certificate
    (J : Ideal S) (E : Submodule S (S ⊗[Ω] ((∀ j : Charts, Bc j) × ∀ j l : Charts, Cc j l)))
    (hE : E.FG)
    (h : ∀ n : ℕ, ∃ z : S ⊗[Ω] (∀ j : Charts, Ac j),
      (D).baseChange S (Pair (1, z)) ∈ J ^ n • E)
    (ρ : S →+* T) (hρ : ρ.comp (algebraMap Ω S) = κ) (hJ : J ≤ RingHom.ker ρ) :
    ∃ a : originalBoundaryLiftIdeal f hL d V c k W t →₀ T,
      a.sum (fun v b ↦ b * (invariantInclusion ec).hom.app (op Wc)
        ((m).c.app (op W) v.val)) = 1 :=
  (mem_originalBoundaryCertifiedSections_iff f hL d V c k W t).mp
    (originalFiniteErrorCorrection_certified f hL d V c k W hW t S J E hE h ρ hρ hJ)

/-- The finite identity covers the original boundary on the original affine-source orbit domain. -/
theorem originalFiniteErrorCorrection_cover
    (J : Ideal S) (E : Submodule S (S ⊗[Ω] ((∀ j : Charts, Bc j) × ∀ j l : Charts, Cc j l)))
    (hE : E.FG)
    (h : ∀ n : ℕ, ∃ z : S ⊗[Ω] (∀ j : Charts, Ac j),
      (D).baseChange S (Pair (1, z)) ∈ J ^ n • E)
    (ρ : S →+* T) (hρ : ρ.comp (algebraMap Ω S) = κ) (hJ : J ≤ RingHom.ker ρ) :
    (TopologicalSpace.Opens.map (m).base).obj
      (originalBoundaryLiftOpen f hL d V c k W t) = Wc :=
  (mem_originalBoundaryCertifiedSections_iff_cover f hL d V c k W t hW).mp
    (originalFiniteErrorCorrection_certified f hL d V c k W hW t S J E hE h ρ hρ hJ)

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
