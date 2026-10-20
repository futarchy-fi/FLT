/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFiniteLocusScalarCoordinates

/-!
# Noetherian original scalars on finite relation domains

The original source is finite type over the integers and finite as a module
over the unchanged invariant scalars. Injectivity and Artin--Tate therefore
make those actual scalars finite type over the integers, hence Noetherian.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Module
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit InvariantOpenRelationDiagram
open SchemeOpenEnvelope SchemeFiniteGroupQuotient
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
/-- Artin--Tate makes the unchanged original invariant scalars finite type over the integers. -/
theorem originalOrbitScalars_integer_finiteType_of_finiteDomain : Algebra.FiniteType ℤ Ω := by
  let _ : IsAffine (E).toScheme := hW
  let _ : LocallyOfFiniteType A.hom := by
    rw [← k.w]
    infer_instance
  let _ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let g := (E).ι ≫ A.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ R))
  let _ : LocallyOfFiniteType g := by dsimp only [g]; infer_instance
  let _ := integerCoordinates_finiteType g
  let _ := (σ).toAlgebra
  let _ : Module.Finite Ω Γ((E).toScheme, ⊤) :=
    originalOrbitSource_scalar_finite_of_finiteDomain f hL d V c k W hW hfin
  exact ⟨fg_of_fg_of_fg ℤ Ω Γ((E).toScheme, ⊤) Algebra.FiniteType.out Module.Finite.fg_top
    (orbitScalarCoordinates_injective eo W)⟩

omit [IsAffine A.left] in
/-- Noetherianity follows for the original scalar ring, without replacing it by a chart ring. -/
theorem originalOrbitScalars_noetherian_of_finiteDomain : IsNoetherianRing Ω := by
  let _ := originalOrbitScalars_integer_finiteType_of_finiteDomain f hL d V c k W hW hfin
  exact Algebra.FiniteType.isNoetherianRing ℤ Ω

end FLT.Mazur.HilbertChart.AffineRestriction
