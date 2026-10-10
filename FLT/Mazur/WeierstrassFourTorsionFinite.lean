/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricSectionQuasiFinite
public import FLT.Mazur.GroupTorsionProper
public import FLT.Mazur.WeierstrassGeometricFourTorsion
public import FLT.Mazur.WeierstrassIntegralProper

/-!
# Finiteness of the actual four-torsion equation

For a smooth Weierstrass cubic with two invertible, its full scheme-theoretic
four-torsion is finite over the coefficient ring. Geometric point counting gives
quasi-finiteness; the closed torsion equation is proper. This does not yet assert
flatness or reduced geometric fibers.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The actual four-torsion equation inside the original smooth cubic group. -/
def integralFourTorsion : Over (Spec (.of R)) :=
  GroupTorsionScheme.scheme (integralCurveGroup W hΔ).X 4

/-- The original group is proper, with its actual Weierstrass structure map. -/
instance integralGroup_structure_proper : IsProper (integralCurveGroup W hΔ).X.hom := by
  change IsProper (integralCurveStructure W)
  infer_instance

/-- Properness holds for the full torsion equation before any smoothness of its fibers. -/
instance integralFourTorsion_proper : IsProper (integralFourTorsion W hΔ).hom :=
  GroupTorsionScheme.structure_proper _ _

/-- Every algebraically closed geometric test sees finitely many actual torsion sections. -/
theorem integralFourTorsion_finite_maps (h2 : IsUnit (2 : R))
    (K : Type) [Field K] [IsAlgClosed K] (g : Spec (.of K) ⟶ Spec (.of R)) :
    Finite (Over.mk g ⟶ integralFourTorsion W hΔ) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  let _ : Algebra R K := φ.hom.toAlgebra
  have h2K : (2 : K) ≠ 0 := by
    have h := h2.map φ.hom
    rw [map_ofNat] at h
    exact h.ne_zero
  have hc := integralFourTorsion_card W hΔ h2K
  have : Finite {P : integralGroupFieldPoints (K := K) W hΔ // P ^ 4 = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; decide)
  exact Finite.of_equiv
    {P : integralGroupFieldPoints (K := K) W hΔ // P ^ 4 = 1}
    (GroupTorsionScheme.representation (integralCurveGroup W hΔ).X 4 (Over.mk (Spec.map φ))).symm

/-- The full four-torsion equation is finite over every allowed coefficient ring. -/
theorem integralFourTorsion_isFinite (h2 : IsUnit (2 : R)) :
    IsFinite (integralFourTorsion W hΔ).hom :=
  GeometricSectionQuasiFinite.isFinite _ (integralFourTorsion_finite_maps W hΔ h2)

end FLT.Mazur.WeierstrassIntegralChart
