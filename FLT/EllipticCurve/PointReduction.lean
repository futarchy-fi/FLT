/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.TorsionSpecialization
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# Coordinate reduction and torsion specialization

For a Weierstrass equation over a valuation subring with elliptic special fiber,
`reducePoint` reduces integral affine coordinates and sends the remaining points
to infinity. It preserves torsion and its restriction `reduceTorsion` is surjective
when the fraction field is algebraically closed and the generic fiber is elliptic.
Inertia fixes these reductions.

Additivity of `reducePoint` remains to be proved. Accordingly `reduceTorsion` is
currently a function, not an additive or linear map.
-/

@[expose] public section

open Polynomial IsLocalRing
namespace WeierstrassCurve

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  [(W.map (residue A)).IsElliptic]

/-- Reduce integral affine coordinates on an elliptic special fiber. -/
theorem nonsingular_residue_of_nonsingular {x y : A}
    (h : (W.map (algebraMap A K)).toAffine.Nonsingular (algebraMap A K x)
      (algebraMap A K y)) : (W.map (residue A)).toAffine.Nonsingular (residue A x)
        (residue A y) := by
  apply Affine.equation_iff_nonsingular.mp
  apply Affine.Equation.map
  exact (W.toAffine.map_equation (IsFractionRing.injective A K) x y).mp h.1

/-- Coordinate reduction, sending points outside the integral affine chart to infinity. -/
noncomputable def reducePoint : (W.map (algebraMap A K)).toAffine.Point →
    (W.map (residue A)).toAffine.Point := by
  classical
  exact fun P => match P with
  | .zero => .zero
  | .some x y h => if hi : x ∈ A ∧ y ∈ A then
      .some (residue A ⟨x, hi.1⟩) (residue A ⟨y, hi.2⟩)
        (W.nonsingular_residue_of_nonsingular A (x := ⟨x, hi.1⟩) (y := ⟨y, hi.2⟩) h)
      else .zero

/-- Infinity reduces to infinity. -/
@[simp] theorem reducePoint_zero : W.reducePoint A 0 = 0 := rfl

/-- Reduction on integral affine coordinates is coefficientwise reduction. -/
@[simp] theorem reducePoint_some (x y : A)
    (h : (W.map (algebraMap A K)).toAffine.Nonsingular (x : K) (y : K)) :
    W.reducePoint A (.some (x : K) (y : K) h) = .some (residue A x) (residue A y)
      (W.nonsingular_residue_of_nonsingular A h) := by
  simp only [reducePoint, show (x : K) ∈ A from x.property,
    show (y : K) ∈ A from y.property, and_self, ↓reduceDIte]

/-- Coordinate reduction preserves the equation of being killed by an integer. -/
theorem nsmul_reducePoint_eq_zero [DecidableEq K] [DecidableEq (ResidueField A)]
    {P : (W.map (algebraMap A K)).toAffine.Point} (n : ℕ) (hn : n • P = 0) :
    n • W.reducePoint A P = 0 := by
  classical
  cases P with
  | zero => exact nsmul_zero n
  | some x y h =>
    by_cases hi : x ∈ A ∧ y ∈ A
    · let a : A := ⟨x, hi.1⟩
      simp only [reducePoint, dite_eq_left hi]
      apply (W.map (residue A)).nsmul_eq_zero_of_isRoot_ΨSq _ n
      have hr := (W.map (algebraMap A K)).isRoot_ΨSq_of_nsmul_eq_zero h n hn
      have ha : (W.ΨSq n).IsRoot a := by
        apply (IsFractionRing.injective A K)
        have hr' : ((W.map (algebraMap A K)).ΨSq n).eval (algebraMap A K a) = 0 := hr
        simpa only [map_zero, ← eval₂_at_apply, ← eval_map, ← map_ΨSq] using hr'
      rw [map_ΨSq]
      exact ha.map
    · simpa only [reducePoint, dite_eq_right hi, ← Affine.Point.zero_def] using
        (nsmul_zero n : n • (0 : (W.map (residue A)).toAffine.Point) = 0)

/-- Coordinate reduction restricted to geometric torsion; additivity is not asserted here. -/
noncomputable def reduceTorsion [DecidableEq K] [DecidableEq (ResidueField A)] (n : ℕ) :
    Submodule.torsionBy ℤ (W.map (algebraMap A K)).toAffine.Point (n : ℤ) →
      Submodule.torsionBy ℤ (W.map (residue A)).toAffine.Point (n : ℤ) := fun P =>
  ⟨W.reducePoint A P.val, by
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
    exact W.nsmul_reducePoint_eq_zero A n
      (by simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using P.property)⟩

/-- Every special-fiber torsion point is the reduction of a generic-fiber torsion point. -/
theorem reduceTorsion_surjective [IsAlgClosed K] [DecidableEq K]
    [DecidableEq (ResidueField A)] [(W.map (algebraMap A K)).IsElliptic]
    {n : ℕ} (hn : 0 < n) : Function.Surjective (W.reduceTorsion A n) := by
  rintro ⟨P, hP⟩
  have ht : n • P = 0 := by
    simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using hP
  cases P with
  | zero => exact ⟨0, rfl⟩
  | some x y h =>
    obtain ⟨a, b, hab, har, hbr, ht⟩ := W.exists_torsion_lifting A h hn ht
    refine ⟨⟨.some _ _ hab, ?_⟩, ?_⟩
    · simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using ht
    · apply Subtype.ext
      change W.reducePoint A (.some _ _ hab) = _
      simp only [ValuationSubring.algebraMap_apply, reducePoint_some, har, hbr]

open scoped Pointwise

/-- Inertia does not change the reduction of affine coordinates, whenever the
transformed coordinates are again a point of the same curve. -/
theorem reducePoint_some_inertia {F : Type*} [Field F] [Algebra F K]
    (σ : A.decompositionSubgroup F) (hσ : σ ∈ A.inertiaSubgroup F)
    {x y : K} (h : (W.map (algebraMap A K)).toAffine.Nonsingular x y)
    (h' : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((σ : K ≃ₐ[F] K) x) ((σ : K ≃ₐ[F] K) y)) :
    W.reducePoint A (.some _ _ h') = W.reducePoint A (.some _ _ h) := by
  classical
  have hint (z : K) : (σ : K ≃ₐ[F] K) z ∈ A ↔ z ∈ A := by
    change (σ : K ≃ₐ[F] K) • z ∈ A ↔ z ∈ A
    have hs : (σ : K ≃ₐ[F] K) • A = A := σ.property
    simpa only [hs] using
      (ValuationSubring.smul_mem_pointwise_smul_iff (g := (σ : K ≃ₐ[F] K)) (S := A)
        (x := z))
  have hres (z : A) : residue A (σ • z) = residue A z := by
    rw [IsLocalRing.ResidueField.residue_smul]
    change MulSemiringAction.toRingAut _ _ σ = 1 at hσ
    exact congrArg (fun e : ResidueField A ≃+* ResidueField A => e (residue A z)) hσ
  by_cases hi : x ∈ A ∧ y ∈ A
  · have hi' : (σ : K ≃ₐ[F] K) x ∈ A ∧ (σ : K ≃ₐ[F] K) y ∈ A :=
      ⟨(hint x).mpr hi.1, (hint y).mpr hi.2⟩
    simp only [reducePoint, dite_eq_left hi, dite_eq_left hi']
    congr 1
    · exact hres ⟨x, hi.1⟩
    · exact hres ⟨y, hi.2⟩
  · have hi' : ¬ ((σ : K ≃ₐ[F] K) x ∈ A ∧ (σ : K ≃ₐ[F] K) y ∈ A) := by
      simpa only [hint] using hi
    simp only [reducePoint, dite_eq_right hi, dite_eq_right hi']

end WeierstrassCurve
