/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantOpenRelationIntegralCoordinates
public import FLT.Mazur.HilbertPrescribedMinimalScalarCharts
public import FLT.Mazur.InvariantOpenFiniteRelation
public import FLT.Mazur.HilbertBoundaryAmbientPresentation

/-!
# Original Hilbert scalars on finite free relation domains

The original relation is affine on its finite target locus. A basis for this
whole relation gives monic equations over the unchanged invariant scalars.
Actual source finite type then proves scalar module finiteness. The finite
locus and basis are geometric inputs, not boundary finiteness assumptions.
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
  {ι : Type*} [Finite ι]
include hW hfin

omit [Etale V.hom] [IsAffine A.left] [IsOpenImmersion k.left] in
/-- Actual finite relation geometry makes the original scalar inclusion integral. -/
theorem originalOrbitSource_scalar_integral_of_basis :
    let _ := (p₀).appTop.hom.toAlgebra
    Basis ι Γ((InvariantOpenRelationDiagram.source E).left, ⊤) Γ(D₀, ⊤) →
      (σ).IsIntegral := by
  let _ : IsAffine (E).toScheme := hW
  let _ := relation_affine_of_le_finiteTarget p E hfin hW
  exact orbitScalarCoordinates_integral_of_basis eo W
    (fullRelationSchemeEquivalence f hL d V c k)

omit [IsAffine A.left] in
/-- Actual finite type supplies module finiteness over the original invariant scalars. -/
theorem originalOrbitSource_scalar_finite_of_basis :
    let _ := (p₀).appTop.hom.toAlgebra
    Basis ι Γ((InvariantOpenRelationDiagram.source E).left, ⊤) Γ(D₀, ⊤) →
      (σ).Finite := by
  let _ := (p₀).appTop.hom.toAlgebra
  dsimp only
  intro basis
  exact (originalOrbitSource_scalar_integral_of_basis f hL d V c k W hW hfin basis).to_finite
    (originalOrbitSource_scalar_finiteType f hL d V c k W hW)

omit [IsAffine A.left] in
/-- The same finiteness holds in the original source sheaf coordinates. -/
theorem originalSourceInclusion_finite_of_basis :
    let _ := (p₀).appTop.hom.toAlgebra
    Basis ι Γ((InvariantOpenRelationDiagram.source E).left, ⊤) Γ(D₀, ⊤) →
      (inc).Finite := by
  let _ := (p₀).appTop.hom.toAlgebra
  dsimp only
  intro basis
  have hf := (sourceFunctions E).symm.finite.comp
    (originalOrbitSource_scalar_finite_of_basis f hL d V c k W hW hfin basis)
  have he : (sourceFunctions E).symm.toRingHom.comp σ = inc := by
    ext a
    apply (sourceFunctions E).injective
    change (sourceFunctions E) ((sourceFunctions E).symm (σ a)) = _
    rw [RingEquiv.apply_symm_apply, orbitScalarCoordinates_apply, orbitFunctions_val]
    rfl
  rwa [he] at hf

end FLT.Mazur.HilbertChart.AffineRestriction
