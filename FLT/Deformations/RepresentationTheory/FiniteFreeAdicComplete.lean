/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Adic completeness of finite free modules

Completeness is proved in a finite basis, rather than requested as additional
input on the original lattice.
-/

@[expose] public noncomputable section
namespace Module.Basis
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (b : Basis ι R M) (I : Ideal R)

/-- Ideal multiples are detected in the coordinates of a basis. -/
theorem mem_ideal_smul_top_iff (x : M) :
    x ∈ I • (⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  rw [← b.span_eq, Submodule.mem_ideal_smul_span_iff_exists_sum]
  constructor
  · rintro ⟨a, ha, rfl⟩
    change ∀ i, b.repr (Finsupp.linearCombination R b a) i ∈ I
    simpa only [b.repr_linearCombination] using ha
  · intro hx
    exact ⟨b.repr x, hx, b.linearCombination_repr x⟩

include b in
/-- Finite free modules over an adically complete ring are adically complete. -/
theorem isAdicComplete [Finite ι] [IsAdicComplete I R] : IsAdicComplete I M := by
  classical
  let := Fintype.ofFinite ι
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply b.repr.injective
    ext i
    simp only [map_zero, Finsupp.zero_apply]
    apply IsHausdorff.haus (inferInstance : IsHausdorff I R)
    intro n
    have hn := (b.mem_ideal_smul_top_iff (I ^ n) x).mp
      (by simpa [SModEq.sub_mem] using hx n) i
    simpa [SModEq.sub_mem, ← Ideal.one_eq_top, smul_eq_mul, mul_one] using hn
  · intro f hf
    have hi (i : ι) : ∃ L : R, ∀ n,
        b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Ideal R)] := by
      apply IsPrecomplete.prec (inferInstance : IsPrecomplete I R)
      intro m n h
      have hn := (b.mem_ideal_smul_top_iff (I ^ m) (f m - f n)).mp
        ((SModEq.sub_mem).mp (hf h)) i
      simpa [SModEq.sub_mem, ← Ideal.one_eq_top, smul_eq_mul, mul_one] using hn
    choose L hL using hi
    refine ⟨b.equivFun.symm L, fun n ↦ ?_⟩
    rw [SModEq.sub_mem, b.mem_ideal_smul_top_iff]
    intro i
    have hi := hL i n
    simpa only [SModEq.sub_mem, ← Ideal.one_eq_top, smul_eq_mul, mul_one,
      map_sub, Finsupp.sub_apply, ← b.equivFun_apply, LinearEquiv.apply_symm_apply] using hi

end Module.Basis
