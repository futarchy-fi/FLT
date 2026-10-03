/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonDivisorPolynomialHZero
public import FLT.Mazur.PolygonCubicInterpolation
/-!
# Cubic interpolation by genuine polygon sections

Transport the weighted polynomial interpolation through actual polygon H0.
The coordinate formula retains pullback to the normalization and component
restriction. These section interpolation statements do not assert generation
at all scheme points or construct a projective morphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching ProjectiveLineMarkedHZero
open PolygonPowerNodeEndpoints PolygonPowerBranchValues
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)
/-- Genuine global sections correspond to weighted matching polynomial families. -/
def sectionEquiv (d : ℕ) : Γ(polygonLine K n hn p q h a (d + 1), ⊤) ≃
    PolygonPolynomialMatching.matching (fun _ : Fin n ↦ d) (finRotate n).symm
      (weight K n a (d + 1)) :=
  (moduleScalarH0Equiv C.hom _).symm.toEquiv.trans (h0PolynomialEquiv K n hn p q h a d)
set_option maxRecDepth 2000 in
/-- Coordinates are computed by actual normalization pullback and component restriction. -/
lemma sectionEquiv_val (d : ℕ) (s : Γ(polygonLine K n hn p q h a (d + 1), ⊤)) :
    (sectionEquiv K n hn p q h a d s).val =
      fun i ↦ polynomialEquiv K (a i) (d + 1)
        (componentClass K n hn p q h a (d + 1)
          (pullGlobal p.left (polygonLine K n hn p q h a (d + 1)) s) i) := by
  change (h0PolynomialEquiv K n hn p q h a d
    ((moduleScalarH0Equiv C.hom _).symm s)).val = _
  rw [h0PolynomialEquiv_val]
  change (fun i ↦ polynomialEquiv K (a i) (d + 1)
    (componentClass K n hn p q h a (d + 1)
      (moduleScalarH0Equiv C.hom _ (moduleScalarHMap C.hom
        ((pullbackPushforwardAdjunction p.left).unit.app _) 0
          ((moduleScalarH0Equiv C.hom _).symm s))) i)) = _
  rw [moduleScalarH0Equiv_naturality, LinearEquiv.apply_symm_apply]
  rfl

/-- A genuine cubic section with prescribed node and branch-linear coefficients. -/
def nodeSection (v b c : Fin n → K) : Γ(polygonLine K n hn p q h a 3, ⊤) :=
  (sectionEquiv K n hn p q h a 2).symm
    (PolygonCubicInterpolation.lift (finRotate n).symm (weight K n a 3) v b c)
/-- The prescribed node and branch-linear coefficients are attained. -/
lemma nodeSection_coefficients (v b c : Fin n → K) (i : Fin n) :
    let P := ((sectionEquiv K n hn p q h a 2 (nodeSection K n hn p q h a v b c)).val i).val
    P.coeff 0 = v i ∧ P.coeff 1 = b i ∧ P.coeff 2 = c i := by
  simp only [nodeSection, Equiv.apply_symm_apply, PolygonCubicInterpolation.lift]
  simp only [PolygonCubicInterpolation.cubic_coeff_zero,
    PolygonCubicInterpolation.cubic_coeff_one, PolygonCubicInterpolation.cubic_coeff_two,
    and_self]
/-- A genuine section realizes an arbitrary nonzero-coordinate polynomial first jet. -/
lemma prescribed_interior_jet (i : Fin n) {z : K} (hz : z ≠ 0) (r t : K) :
    ∃ s : Γ(polygonLine K n hn p q h a 3, ⊤),
      let P := (sectionEquiv K n hn p q h a 2 s).val
      (P i).val.eval z = r ∧ (Polynomial.derivative (P i).val).eval z = t ∧
        (∀ j, (P j).val.coeff 0 = 0) ∧ (∀ j, j ≠ i → (P j).val = 0) := by
  obtain ⟨P, hP⟩ := PolygonCubicInterpolation.prescribed_interior_jet
    (finRotate n).symm (weight K n a 3) i hz r t
  refine ⟨(sectionEquiv K n hn p q h a 2).symm P, ?_⟩
  simpa only [Equiv.apply_symm_apply] using hP
end FLT.Mazur.PolygonCubicSections
