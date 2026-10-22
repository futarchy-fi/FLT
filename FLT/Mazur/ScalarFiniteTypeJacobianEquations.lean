/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarPresentationResidueGradients
public import FLT.Mazur.ScalarJacobianRowSelection

/-!
# Constructing exact square systems from finite type and a zero differential fiber

Finite type constructs polynomial coordinates on the source ring itself. The
conormal sequence supplies spanning gradients, and basis selection chooses
finitely many genuine kernel relations. The equations hold before passage to
any residue field or localization, including on the nonreduced source.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarFiniteTypeJacobianEquations
open Algebra MvPolynomial TensorProduct
variable {R A K : Type} [CommRing R] [CommRing A] [Field K]
  [Algebra R A] [Algebra A K]
  [Subsingleton (K ⊗[A] KaehlerDifferential R A)]

/-- A finite source presentation constructs distinct kernel relations with nonzero determinant. -/
theorem exists_relations {n : ℕ} (P : Generators R A (Fin n)) :
    ∃ F : Fin n → P.ker, Function.Injective F ∧
      Matrix.det (fun i j ↦ algebraMap A K (aeval P.val (pderiv j (F i).val))) ≠ 0 := by
  exact ScalarJacobianRowSelection.exists_nonsingular n _
    (ScalarPresentationResidueGradients.span_eq_top (K := K) P)

/-- Finite type constructs coordinates and exact equations, without finite type of the stalk. -/
theorem exists_equations [FiniteType R A] :
    ∃ (n : ℕ) (z : Fin n → A) (F : Fin n → MvPolynomial (Fin n) R),
      Algebra.adjoin R (Set.range z) = ⊤ ∧
      (∀ i, aeval z (F i) = 0) ∧
      Matrix.det (fun i j ↦ algebraMap A K (aeval z (pderiv j (F i)))) ≠ 0 := by
  obtain ⟨n, ⟨P⟩⟩ := (FiniteType.iff_exists_generators (R := R) (S := A)).mp inferInstance
  obtain ⟨F, _, hF⟩ := exists_relations (K := K) P
  refine ⟨n, P.val, fun i ↦ (F i).val, ?_, ?_, hF⟩
  · rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top]
    exact P.aeval_val_surjective
  · intro i
    exact P.aeval_val_eq_zero (F i).property

variable {k : Type} [CommRing k] [Algebra k R] [Algebra k A] [IsScalarTower k R A]

/-- Finite type over a smaller base supplies the exact-scalar polynomial presentation. -/
theorem exists_equations_of_base [FiniteType k A] :
    ∃ (n : ℕ) (z : Fin n → A) (F : Fin n → MvPolynomial (Fin n) R),
      Algebra.adjoin R (Set.range z) = ⊤ ∧
      (∀ i, aeval z (F i) = 0) ∧
      Matrix.det (fun i j ↦ algebraMap A K (aeval z (pderiv j (F i)))) ≠ 0 := by
  let _ : FiniteType R A := FiniteType.of_restrictScalars_finiteType k R A
  exact exists_equations

end FLT.Mazur.ScalarFiniteTypeJacobianEquations
