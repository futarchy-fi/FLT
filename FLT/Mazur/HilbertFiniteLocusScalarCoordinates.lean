/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantOpenProjectiveIntegralCoordinates
public import FLT.Mazur.HilbertPrescribedMinimalScalarCharts
public import FLT.Mazur.InvariantOpenFiniteRelation
public import FLT.Mazur.HilbertBoundaryAmbientPresentation

/-!
# Original Hilbert scalars on finite relation domains

The whole original relation is finite projective over an affine domain inside
its finite target locus. Actual local bases and invariant monic equations
therefore prove scalar module finiteness without any basis hypothesis.
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

omit [IsAffine A.left] in
/-- The actual finite relation geometry makes the original scalar inclusion integral. -/
theorem originalOrbitSource_scalar_integral_of_finiteDomain : (σ).IsIntegral := by
  let _ : IsAffine (E).toScheme := hW
  let _ : IsAffine (InvariantOpenRelationDiagram.source E).left := hW
  let _ := relation_affine_of_le_finiteTarget p E hfin hW
  let _ := fst_finite_of_le_finiteTarget p E hfin
  exact orbitScalarCoordinates_integral_of_projective eo W
    (fullRelationSchemeEquivalence f hL d V c k) (p₀).finite_appTop
    (fst_projective_of_le_finiteTarget p E hfin hW)

omit [IsAffine A.left] in
/-- Actual finite type supplies module finiteness over the original invariant scalars. -/
theorem originalOrbitSource_scalar_finite_of_finiteDomain :
    (σ).Finite := by
  exact (originalOrbitSource_scalar_integral_of_finiteDomain f hL d V c k W hW hfin).to_finite
    (originalOrbitSource_scalar_finiteType f hL d V c k W hW)

omit [IsAffine A.left] in
/-- The same finiteness holds in the original source sheaf coordinates. -/
theorem originalSourceInclusion_finite_of_finiteDomain :
    (inc).Finite := by
  have hf := (sourceFunctions E).symm.finite.comp
    (originalOrbitSource_scalar_finite_of_finiteDomain f hL d V c k W hW hfin)
  have he : (sourceFunctions E).symm.toRingHom.comp σ = inc := by
    ext a
    apply (sourceFunctions E).injective
    change (sourceFunctions E) ((sourceFunctions E).symm (σ a)) = _
    rw [RingEquiv.apply_symm_apply, orbitScalarCoordinates_apply, orbitFunctions_val]
    rfl
  rwa [he] at hf

end FLT.Mazur.HilbertChart.AffineRestriction
