/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFiniteTargetSaturation
public import FLT.Mazur.FiniteTargetOrbitAffineBasis

/-!
# Affine invariant refinements of the original Hilbert finite locus

Every point in the exact finite locus now has an actual orbit neighborhood
whose whole original source is affine and whose whole relation is finite.
The entire finite locus is covered by these domains, without being assumed affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "e" => equivalence f hL d V c k
attribute [local irreducible] relation fst snd equivalence

/-- Original finite-locus points have finite affine source neighborhoods in any orbit open. -/
theorem exists_originalFiniteAffine_neighborhood
    (W : TopologicalSpace.Opens (Orbit e)) (x : A.left)
    (hx : projection e x ∈ W) (hf : x ∈ finiteTargetOpen (p).left) :
    ∃ Z : TopologicalSpace.Opens (Orbit e), projection e x ∈ Z ∧ Z ≤ W ∧
      IsAffineOpen (pullOpen e Z).val ∧ (pullOpen e Z).val ≤ finiteTargetOpen (p).left := by
  let _ : LocallyQuasiFinite (p).left :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)
  exact exists_finite_affine_orbit_neighborhood e
    (fullRelationSchemeEquivalence f hL d V c k) W x hx hf

/-- The entire original finite orbit locus is covered by constructed affine source domains. -/
theorem originalFiniteOrbitOpen_affine_cover :
    (⨆ (Z : TopologicalSpace.Opens (Orbit e))
      (_ : Z ≤ originalFiniteOrbitOpen f hL d V c k)
      (_ : IsAffineOpen (pullOpen e Z).val), Z) = originalFiniteOrbitOpen f hL d V c k := by
  let _ : LocallyQuasiFinite (p).left :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)
  apply finite_affine_orbit_cover e (fullRelationSchemeEquivalence f hL d V c k)
  rw [pullOpen_originalFiniteOrbitOpen]

end FLT.Mazur.HilbertChart.AffineRestriction
