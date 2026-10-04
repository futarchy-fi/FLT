/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.GeometricPointLocalization
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Geometric points above each prime of an original polynomial presentation -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] {n : ℕ}

/-- The residue-field geometric point factors through the original presented algebra,
and its contracted coordinate ideal is exactly the specified original prime. -/
theorem exists_geometric_point_over_prime
    (f : MvPolynomial (Fin n) k →ₐ[k] A) (hf : Function.Surjective f)
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] (hP : RingHom.ker f ≤ P) :
    ∃ y : A →ₐ[k] AlgebraicClosure P.ResidueField,
      (rationalPointIdeal (fun i ↦ y (f (X i)))).comap
        (map (algebraMap k (AlgebraicClosure P.ResidueField))) = P := by
  let Ω := AlgebraicClosure P.ResidueField
  let g : MvPolynomial (Fin n) k →ₐ[k] Ω :=
    (IsScalarTower.toAlgHom k P.ResidueField Ω).comp
      (IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k) P.ResidueField)
  have hg : RingHom.ker g = P := by
    ext q
    change algebraMap P.ResidueField Ω (algebraMap _ P.ResidueField q) = 0 ↔ q ∈ P
    rw [map_eq_zero, Ideal.algebraMap_residueField_eq_zero]
  let y := f.liftOfSurjective hf g (by
    change RingHom.ker f ≤ RingHom.ker g
    rwa [hg])
  refine ⟨y, ?_⟩
  have hc : (aeval (R := k) (fun i ↦ y (f (X i)))) = g := by
    ext i
    simp [y]
  ext q
  change aeval (R := Ω) (fun i ↦ y (f (X i))) (map (algebraMap k Ω) q) = 0 ↔ q ∈ P
  rw [aeval_map_algebraMap, hc]
  exact SetLike.ext_iff.mp hg q

end MvPolynomial
