/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricSectionQuasiFinite
public import FLT.Mazur.GroupTorsionProper
public import FLT.Mazur.WeierstrassGeometricThreeTorsion
public import FLT.Mazur.WeierstrassFourTorsionFinite

/-!
# Finiteness of the actual three-torsion equation

For a smooth Weierstrass cubic with three invertible, its full scheme-theoretic
three-torsion is finite over the coefficient ring. Geometric point counting gives
quasi-finiteness; the closed torsion equation is proper. This does not yet assert
flatness or reduced geometric fibers.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The actual three-torsion equation inside the original smooth cubic group. -/
def integralThreeTorsion : Over (Spec (.of R)) :=
  GroupTorsionScheme.scheme (integralCurveGroup W hΔ).X 3

/-- Properness holds for the full torsion equation before any smoothness of its fibers. -/
instance integralThreeTorsion_proper : IsProper (integralThreeTorsion W hΔ).hom :=
  GroupTorsionScheme.structure_proper _ _

/-- Every algebraically closed geometric test sees finitely many actual torsion sections. -/
theorem integralThreeTorsion_finite_maps (h3 : IsUnit (3 : R))
    (K : Type) [Field K] [IsAlgClosed K] (g : Spec (.of K) ⟶ Spec (.of R)) :
    Finite (Over.mk g ⟶ integralThreeTorsion W hΔ) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  let _ : Algebra R K := φ.hom.toAlgebra
  have h3K : (3 : K) ≠ 0 := by
    have h := h3.map φ.hom
    rw [map_ofNat] at h
    exact h.ne_zero
  have hc := integralThreeTorsion_card W hΔ h3K
  have : Finite {P : integralGroupFieldPoints (K := K) W hΔ // P ^ 3 = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; decide)
  exact Finite.of_equiv
    {P : integralGroupFieldPoints (K := K) W hΔ // P ^ 3 = 1}
    (GroupTorsionScheme.representation (integralCurveGroup W hΔ).X 3 (Over.mk (Spec.map φ))).symm

/-- The full three-torsion equation is finite over every allowed coefficient ring. -/
theorem integralThreeTorsion_isFinite (h3 : IsUnit (3 : R)) :
    IsFinite (integralThreeTorsion W hΔ).hom :=
  GeometricSectionQuasiFinite.isFinite _ (integralThreeTorsion_finite_maps W hΔ h3)

end FLT.Mazur.WeierstrassIntegralChart
