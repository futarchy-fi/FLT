/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.GraphIdeal

/-! # Regular sequences after adjoining redundant coordinates -/

@[expose] public noncomputable section

namespace MvPolynomial

open RingTheory.Sequence

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The ordered graph equations generate the evaluation kernel. -/
theorem ker_eval_eq_graph_list (a : Fin n → R) :
    RingHom.ker (eval a) = Ideal.ofList ((List.finRange n).map fun i ↦ X i - C (a i)) := by
  rw [ker_eval_eq_graph]
  congr 1
  ext p
  simp

/-- Quotienting by the graph equations recovers the coefficient ring. -/
def graphQuotientEquiv (a : Fin n → R) :
    (MvPolynomial (Fin n) R ⧸
      Ideal.ofList ((List.finRange n).map fun i ↦ X i - C (a i))) ≃ₐ[R] R := by
  have hk : RingHom.ker (aeval (R := R) a) =
      Ideal.ofList ((List.finRange n).map fun i ↦ X i - C (a i)) := by
    convert ker_eval_eq_graph_list a using 1
    ext p
    exact Iff.rfl
  let e : (MvPolynomial (Fin n) R ⧸ RingHom.ker (aeval (R := R) a)) ≃ₐ[R] R :=
    Ideal.quotientKerAlgEquivOfSurjective (f := aeval (R := R) a)
      (fun r ↦ ⟨C r, aeval_C a r⟩)
  exact (Ideal.quotientEquivAlgOfEq R hk.symm).trans e

/-- The graph quotient keeps the specified evaluation on polynomial representatives. -/
@[simp] theorem graphQuotientEquiv_mk (a : Fin n → R) (p : MvPolynomial (Fin n) R) :
    graphQuotientEquiv a (Ideal.Quotient.mk _ p) = eval a p := rfl

/-- Adding graph equations before the original relations preserves regularity and order. -/
theorem isRegular_graph_append (a : Fin n → R) (rs : List R) (hreg : IsRegular R rs) :
    IsRegular (MvPolynomial (Fin n) R)
      (((List.finRange n).map fun i ↦ X i - C (a i)) ++ rs.map C) := by
  have := hreg.nontrivial
  let gs : List (MvPolynomial (Fin n) R) :=
    (List.finRange n).map fun i ↦ X i - C (a i)
  have hg : IsRegular (MvPolynomial (Fin n) R) gs :=
    isRegular_X_sub_C_list a (List.nodup_finRange n)
  refine ⟨(isWeaklyRegular_append_iff _ gs (rs.map C)).mpr ⟨hg.1, ?_⟩, ?_⟩
  · rw [Ideal.smul_eq_mul, Ideal.mul_top]
    have hq : IsWeaklyRegular (MvPolynomial (Fin n) R ⧸ Ideal.ofList gs) rs :=
      ((graphQuotientEquiv a).toLinearEquiv.isWeaklyRegular_congr rs).mpr hreg.1
    exact (isWeaklyRegular_map_algebraMap_iff (MvPolynomial (Fin n) R) _ rs).mpr hq
  · rw [Ideal.smul_eq_mul, Ideal.mul_top]
    intro ht
    have hmem : (1 : MvPolynomial (Fin n) R) ∈ Ideal.ofList (gs ++ rs.map C) :=
      ht ▸ (show (1 : MvPolynomial (Fin n) R) ∈ (⊤ : Ideal _) from trivial)
    have hid : Ideal.ofList (gs ++ rs.map C) = (Ideal.ofList rs).comap (eval a) := by
      rw [comap_eval_eq_graph_sup, Ideal.ofList_append, Ideal.map_ofList]
      congr 1
      exact (ker_eval_eq_graph_list a).symm.trans (ker_eval_eq_graph a)
    rw [hid] at hmem
    have hone : (1 : R) ∈ Ideal.ofList rs := by simpa using hmem
    apply hreg.2
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.eq_top_of_isUnit_mem _ hone isUnit_one]

end MvPolynomial
