/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ValuationProjectiveNormalization
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
# Projective reduction without a good-reduction assumption

A generic-fiber point admits primitive integral projective coordinates. Reducing
these coordinates gives a well-defined projective class satisfying the special
cubic equation. Its reduction may be singular: this construction retains that
class instead of treating it as a point in the smooth special-fiber group.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve WeierstrassCurve.Projective

variable {K : Type*} [Field K] (A : ValuationSubring K)

/-- Primitive integral coordinates representing a specified generic projective class. -/
structure PrimitiveLift (P : PointClass K) where
  /-- The integral coordinate vector. -/
  coords : Fin 3 → A
  /-- At least one coordinate is a unit. -/
  primitive : UnitCoordinate A coords
  /-- Its generic class is the specified point. -/
  represents : (⟦fun i => (coords i : K)⟧ : PointClass K) = P

/-- The residue class of primitive integral coordinates. -/
def PrimitiveLift.reduction {P : PointClass K} (v : PrimitiveLift A P) :
    PointClass (ResidueField A) := ⟦residue A ∘ v.coords⟧

/-- All primitive integral representatives give the same residue class. -/
theorem PrimitiveLift.reduction_eq {P : PointClass K} (v w : PrimitiveLift A P) :
    v.reduction = w.reduction :=
  Quotient.sound (residue_equiv_of_generic_equiv A v.primitive w.primitive
    (Quotient.exact (v.represents.trans w.represents.symm)))

variable (W : WeierstrassCurve A)

/-- Every actual generic-fiber point has primitive integral coordinates. -/
theorem exists_primitiveLift (P : (W.map (algebraMap A K)).toProjective.Point) :
    Nonempty (PrimitiveLift A P.point) := by
  obtain ⟨v, hv⟩ := Quotient.exists_rep P.point
  have hn : (W.map (algebraMap A K)).toProjective.Nonsingular v := by
    have h := P.nonsingular
    rw [← hv] at h
    exact h
  have hne : ∃ i, v i ≠ 0 := by
    by_cases hz : v 2 = 0
    · exact ⟨1, (isUnit_Y_of_Z_eq_zero hn hz).ne_zero⟩
    · exact ⟨2, hz⟩
  obtain ⟨w, u, hw, hu⟩ := exists_primitive_coordinates A v hne
  refine ⟨⟨w, hw, ?_⟩⟩
  rw [hu]
  exact (show (⟦u • v⟧ : PointClass K) = ⟦v⟧ from Quotient.sound ⟨u, rfl⟩).trans hv

/-- A chosen primitive representative; reduction below is independent of this choice. -/
noncomputable def primitiveLift (P : (W.map (algebraMap A K)).toProjective.Point) :
    PrimitiveLift A P.point := Classical.choice (exists_primitiveLift A W P)

/-- Reduction of an actual point to the projective special cubic, possibly singular. -/
noncomputable def projectiveReduction
    (P : (W.map (algebraMap A K)).toProjective.Point) : PointClass (ResidueField A) :=
  (primitiveLift A W P).reduction

/-- Compute reduction from any primitive integral representative. -/
theorem projectiveReduction_eq
    (P : (W.map (algebraMap A K)).toProjective.Point) (v : PrimitiveLift A P.point) :
    projectiveReduction A W P = v.reduction :=
  PrimitiveLift.reduction_eq A _ _

/-- Primitive coordinates of a generic point satisfy the integral cubic equation. -/
theorem PrimitiveLift.equation
    {P : (W.map (algebraMap A K)).toProjective.Point} (v : PrimitiveLift A P.point) :
    W.toProjective.Equation v.coords := by
  apply (W.toProjective.map_equation (IsFractionRing.injective A K) v.coords).mp
  have h := P.nonsingular
  rw [← v.represents] at h
  exact h.1

/-- The reduced vector satisfies the special cubic equation. -/
theorem PrimitiveLift.residue_equation
    {P : (W.map (algebraMap A K)).toProjective.Point} (v : PrimitiveLift A P.point) :
    (W.map (residue A)).toProjective.Equation (residue A ∘ v.coords) :=
  (v.equation A W).map (residue A)

/-- Primitive reduction is a nonzero vector, so it defines a genuine projective point. -/
theorem PrimitiveLift.residue_ne_zero {P : PointClass K} (v : PrimitiveLift A P) :
    ∃ i, (residue A ∘ v.coords) i ≠ 0 := by
  obtain ⟨i, hi⟩ := v.primitive
  exact ⟨i, (residue_ne_zero_iff_isUnit _).mpr hi⟩

/-- Infinity has its usual primitive integral representative. -/
def infinityPrimitiveLift : PrimitiveLift A
    (0 : (W.map (algebraMap A K)).toProjective.Point).point where
  coords := ![0, 1, 0]
  primitive := ⟨1, isUnit_one⟩
  represents := by
    apply congrArg Quotient.mk''
    ext i
    fin_cases i <;> simp

/-- Infinity reduces to infinity for every integral Weierstrass equation. -/
@[simp] theorem projectiveReduction_zero :
    projectiveReduction A W 0 = ⟦![0, 1, 0]⟧ := by
  rw [projectiveReduction_eq A W 0 (infinityPrimitiveLift A W)]
  change (⟦residue A ∘ ![0, 1, 0]⟧ : PointClass (ResidueField A)) = _
  simp only [comp_fin3, map_zero, map_one]

/-- An integral affine generic point has the expected reduced homogeneous coordinates. -/
theorem projectiveReduction_affine (x y : A)
    (h : (W.map (algebraMap A K)).toAffine.Nonsingular (x : K) (y : K)) :
    projectiveReduction A W (Affine.Point.toProjective (.some _ _ h)) =
      ⟦![residue A x, residue A y, 1]⟧ := by
  let v : PrimitiveLift A (Affine.Point.toProjective (.some _ _ h)).point :=
    { coords := ![x, y, 1]
      primitive := ⟨2, isUnit_one⟩
      represents := by
        apply congrArg Quotient.mk''
        ext i
        fin_cases i <;> simp }
  rw [projectiveReduction_eq A W _ v]
  change (⟦residue A ∘ ![x, y, 1]⟧ : PointClass (ResidueField A)) = _
  simp only [comp_fin3, map_one]

end FLT.Mazur
