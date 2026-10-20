/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFiniteLocusScalarNoetherian

/-!
# Integral boundary sections from the actual finite source relation

The ambient closed restriction carries the constructed scalar finiteness to
the entire original boundary source. Injectivity of the invariant inclusion
then proves that every original invariant boundary section is integral.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Module
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit InvariantOpenRelationDiagram
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "eo" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen eo W).val
local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "σ" => orbitScalarCoordinates eo W
local notation "p₀" => (InvariantOpenRelationDiagram.fst p E).left
local notation "D₀" => (InvariantOpenRelationDiagram.relation p E).left
local notation "Q" => (sourceSheaf eo).obj.obj (op W)
local notation "inc" => ((invariantInclusion eo).hom.app (op W)).hom
attribute [local irreducible] relation fst snd equivalence invariantSheaf
  invariantInclusion orbitScalarCoordinates
variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
  (hfin : (pullOpen (equivalence f hL d V c k) W).val ≤
    finiteTargetOpen (fst f hL d V c k).left)
include hW hfin

local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "ib" => ((invariantInclusion ec).hom.app (op Wc)).hom
local notation "ρ" => originalClosedSectionPullback f hL d V c k W
local notation "κ" => (ib).comp ρ
local notation "r₀" => originalAmbientBoundaryRestriction f hL d V c k W
attribute [local irreducible] originalClosedEquivalence originalClosedInvariantMap
  originalAmbientBoundaryRestriction originalClosedSectionPullback

/-- The whole ambient boundary source is finite over the unchanged original invariant scalars. -/
theorem originalAmbientBoundary_scalar_finite_of_finiteDomain :
      (κ).Finite := by
  have hf := (RingHom.Finite.of_surjective r₀
    (originalAmbientBoundaryRestriction_surjective f hL d V c k W hW)).comp
      (originalSourceInclusion_finite_of_finiteDomain f hL d V c k W hW hfin)
  have he : (r₀).comp inc = κ := by
    ext a
    exact originalAmbientBoundaryRestriction_invariant f hL d V c k W a
  rwa [he] at hf

/-- Every invariant boundary section satisfies a monic equation over the original scalars. -/
theorem originalClosedSectionPullback_integral_of_finiteDomain :
      (ρ).IsIntegral := by
  exact RingHom.IsIntegral.tower_bot ρ ib (fun _ _ h ↦ invariantSection_ext ec Wc h)
    (originalAmbientBoundary_scalar_finite_of_finiteDomain f hL d V c k W hW hfin).to_isIntegral

/-- Constructed Noetherian original scalars make the entire invariant boundary module finite. -/
theorem originalClosedSectionPullback_finite_of_finiteDomain :
      (ρ).Finite := by
  let _ := originalOrbitScalars_noetherian_of_finiteDomain f hL d V c k W hW hfin
  let _ := (ρ).toAlgebra
  let _ := (κ).toAlgebra
  let _ : Module.Finite Ω ((sourceSheaf ec).obj.obj (op Wc)) :=
    originalAmbientBoundary_scalar_finite_of_finiteDomain f hL d V c k W hW hfin
  let j : (invariantSheaf ec).obj.obj (op Wc) →ₐ[Ω]
      (sourceSheaf ec).obj.obj (op Wc) := { ib with commutes' := fun _ ↦ rfl }
  exact Module.Finite.of_injective j.toLinearMap (fun _ _ h ↦ invariantSection_ext ec Wc h)

end FLT.Mazur.HilbertChart.AffineRestriction
