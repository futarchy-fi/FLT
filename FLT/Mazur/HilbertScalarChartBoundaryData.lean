/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertRequiredScalarFiniteCover
public import FLT.Mazur.HilbertSourceOpenRelationLifts

/-!
# Actual boundary data on the whole-complete scalar charts

The chart uses the original invariant scalar ring and the exact original
boundary pullback. Choose a boundary lift once on the ambient chart. It
satisfies full relation equations on every supported scalar test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeOpenEnvelope
open RelativeRelationOrbit SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
attribute [local irreducible] relation fst snd equivalence

local notation "eo" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen eo W).val
local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "s" => orbitScalarCoordinates eo W

attribute [local irreducible] invariantSheaf orbitScalarCoordinates
  EquivalenceRelationNormalizedFrames.source first completeInterior Complete
  scalarMorphism finiteTargetOpen

local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
attribute [local irreducible] originalClosedEquivalence originalClosedInvariantMap
  normalizedOriginalBoundaryInclusion normalizedOriginalBoundaryAction
  normalizedOriginalScalarMap

namespace OriginalScalarAffineChart
variable {f hL d V c k W} (C : OriginalScalarAffineChart f hL d V c k W)
local notation "ρ" => restrictedAction
  (normalizedFullRelationAction f hL d V c k C.size C.label) C.domain C.stable
local notation "σ" => normalizedOriginalScalarMap f hL d V c k C.size C.label W
  C.domain C.stable C.overDomain
local notation "j" => C.domain.ι ≫ normalizedFullRelationFirst f hL d V c k C.size C.label

/-- The actual chart morphism to the unchanged original scalar spectrum. -/
@[irreducible] def sourceScalars : C.domain.toScheme ⟶ Spec (.of Ω) :=
  quotientMap ρ ≫ Spec.map (CommRingCat.ofHom σ)

/-- The full first chart endpoint, before any scalar base change. -/
abbrev fullFirst := SchemeRelationRestriction.fst p q j

/-- The independent full second chart endpoint. -/
abbrev fullSecond := SchemeRelationRestriction.snd p q j

omit [Etale V.hom] in
/-- Both full endpoints lie over the same original invariant scalars. -/
theorem full_scalar_square : C.fullFirst ≫ C.sourceScalars = C.fullSecond ≫ C.sourceScalars := by
  rw [sourceScalars, ← scalarMorphism_through_quotient,
    ← scalarMorphism_comp, ← scalarMorphism_comp]
  congr 1
  ext a
  exact normalizedOriginalScalarMap_full_source_relation f hL d V c k C.size C.label W
    C.domain C.stable C.overDomain a

/-- The actual original closed boundary inclusion on this chart. -/
abbrev boundaryInclusion :=
  normalizedOriginalBoundaryInclusion f hL d V c k C.size C.label ∣_ C.domain

/-- The original boundary sheaf section restricted to the actual chart boundary. -/
@[irreducible] def boundaryValue (t : (invariantSheaf ec).obj.obj (op Wc)) :
    Γ(((normalizedOriginalBoundaryInclusion f hL d V c k C.size C.label)
      ⁻¹ᵁ C.domain).toScheme, ⊤) :=
  (normalizedOrbitBoundaryCoefficient f hL d V c k C.size C.label W
    C.domain C.stable C.overDomain t).val

/-- A single ambient invariant lift, chosen before the scalar test or infinitesimal order. -/
@[irreducible] def boundaryLift (t : (invariantSheaf ec).obj.obj (op Wc)) :
    invariantCoordinates ρ :=
  (normalizedOrbitBoundaryCoefficient_lift f hL d V c k C.size C.label W
    C.domain C.stable C.overDomain t C.affine).choose

/-- The chosen lift has exactly the prescribed original boundary value. -/
theorem boundaryLift_restrict (t : (invariantSheaf ec).obj.obj (op Wc)) :
    C.boundaryInclusion.appTop (C.boundaryLift t).val = C.boundaryValue t := by
  have h := (normalizedOrbitBoundaryCoefficient_lift f hL d V c k C.size C.label W
    C.domain C.stable C.overDomain t C.affine).choose_spec
  simpa only [boundaryLift, boundaryValue, normalizedBoundaryChartMap, invariantMap_val]
    using congrArg Subtype.val h

/-- That same ambient lift solves all full relation equations on every supported scalar test. -/
theorem boundaryLift_equalizes (t : (invariantSheaf ec).obj.obj (op Wc))
    {Y : Scheme} (b : Y ⟶ Spec (.of Ω)) (hb : ∀ y : Y, b y ∈ C.wholeLocus) :
    (pullback.fst (C.fullFirst ≫ C.sourceScalars) b ≫ C.fullFirst).appTop
        (C.boundaryLift t).val =
      (pullback.fst (C.fullFirst ≫ C.sourceScalars) b ≫ C.fullSecond).appTop
        (C.boundaryLift t).val := by
  let _ : IsAffine C.domain.toScheme := C.affine
  have h := C.scalarTestEqualizes_of_support b hb
  rw [scalarTestEqualizes] at h
  unfold sourceScalars
  exact h (C.boundaryLift t)

end OriginalScalarAffineChart
end FLT.Mazur.HilbertChart.AffineRestriction
