/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitRelativeSourceGenerators
public import FLT.Mazur.LocalizedImageFiniteLifts

/-!
# Common original denominators for the actual relative source image

A finite original boundary family spanning modulo invariant restrictions
tests the actual localized relative map by finitely many original invariant
lifts with one denominator. No global annihilator or geometric finiteness
is inferred from local image finiteness.
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
local notation "i" => Over.Hom.left (originalBoundarySourceMap f hL d V c k)
local notation "ef" => fullRelationSchemeEquivalence f hL d V c k
local notation "o" => fun j : Charts ↦ j.val.label
local notation "U" => fun j : Charts ↦ j.val.domain
local notation "hU" => fun j : Charts ↦ j.val.stable
local notation "Cmix" => (∀ j l : Charts, Cc j l)

attribute [local irreducible] originalMixedBoundaryKernel originalBoundaryMixedCorrectionImage
local notation "N" => originalMixedBoundaryKernel f hL d V c k W hW
local notation "K" => originalBoundaryMixedCorrectionImage f hL d V c k W hW

attribute [local irreducible] originalRelativeMixedConnectingMap
  originalRelativeMixedError originalBoundaryLiftErrorClass
  originalBoundaryExtendedCokernelAddCommGroup originalBoundaryExtendedCokernelModule
  invariantSheaf originalClosedEquivalence originalClosedInvariantMap
  originalBoundarySource originalBoundarySourceMap originalClosedRelation
  originalClosedFst originalClosedSnd originalClosedArrow
local notation "g" => originalRelativeMixedConnectingMap f hL d V c k W hW

variable (S : Type*) [CommRing S]
  [Algebra ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)) S]

attribute [local irreducible] originalBoundaryPullbackLinearMap
local notation "r" => originalBoundaryPullbackLinearMap f hL d V c k W

variable (T : Submonoid ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)))
  [IsLocalization T S]

/-- Exact lifts of a finite relative source frame detect the whole actual local error map. -/
theorem originalRelativeScalarMap_eq_zero_iff_finite_lifts {n : ℕ} (t : Fin n → D)
    (hspan : Submodule.span S (Set.range (fun j ↦ (1 ⊗ₜ[Ω] t j : S ⊗[Ω] D))) ⊔
      LinearMap.range ((r).baseChange S) = ⊤) :
    (g).baseChange S = 0 ↔ ∃ (a : T) (v : Fin n → Ω), ∀ j, r (v j) = a.val • t j :=
  LocalizedImageFiniteLifts.eq_zero_iff_finite_lifts r g
    (originalRelativeMixedConnectingMap_ker f hL d V c k W hW) T S t hspan

/-- Local image finiteness supplies the actual finite original invariant lift test. -/
theorem originalRelativeScalarImage_finite_lift_test
    (hfg : (LinearMap.range ((g).baseChange S)).FG) :
    ∃ (n : ℕ) (t : Fin n → D),
      (Submodule.span S (Set.range (fun j ↦ (1 ⊗ₜ[Ω] t j : S ⊗[Ω] D))) ⊔
        LinearMap.range ((r).baseChange S) = ⊤) ∧
      ((g).baseChange S = 0 ↔ ∃ (a : T) (v : Fin n → Ω), ∀ j, r (v j) = a.val • t j) :=
  LocalizedImageFiniteLifts.exists_finite_lift_test r g
    (originalRelativeMixedConnectingMap_ker f hL d V c k W hW) T S hfg

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
