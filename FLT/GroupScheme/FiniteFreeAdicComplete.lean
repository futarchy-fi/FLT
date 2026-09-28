/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Adic completeness of finite free modules

A finite basis transfers adic Cauchy sequences and their limits coordinatewise.
In particular finite free algebras over a complete base are complete for the
extended ideal. This supplies Henselian pairs for three-adic coordinate rings.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Membership in an ideal multiple of a free module is tested on basis coordinates. -/
theorem basis_mem_ideal_smul_top_iff {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R M) (I : Ideal R) (x : M) :
    x ∈ I • (⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    have hmap := Submodule.mem_map_of_mem (f := b.coord i) hx
    rw [Submodule.map_smul''] at hmap
    exact (Submodule.smul_le.mpr fun r hr y _ ↦ I.mul_mem_right y hr) hmap
  · intro hx
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hx i) (Submodule.mem_top)

/-- A finite basis over an adically complete ring makes its module adically complete. -/
theorem adicComplete_of_finite_basis {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R M) (I : Ideal R) [IsAdicComplete I R] : IsAdicComplete I M := by
  have hcoord (J : Ideal R) (x y : M) :
      x ≡ y [SMOD J • (⊤ : Submodule R M)] ↔
        ∀ i, b.repr x i ≡ b.repr y i [SMOD J] := by
    simp only [SModEq.sub_mem, basis_mem_ideal_smul_top_iff b, map_sub, Finsupp.sub_apply]
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply b.repr.injective
    ext i
    have hz := IsHausdorff.haus (inferInstance : IsHausdorff I R) (b.repr x i)
      (fun n ↦ by simpa using (hcoord (I ^ n) x 0).mp (hx n) i)
    simpa using hz
  · intro f hf
    have hc (i : ι) : ∃ r : R, ∀ n, b.repr (f n) i ≡ r [SMOD I ^ n] := by
      have hh := IsPrecomplete.prec (inferInstance : IsPrecomplete I R)
        (f := fun n ↦ b.repr (f n) i) (fun {m n} hmn ↦ by
          simpa using (hcoord (I ^ m) (f m) (f n)).mp (hf hmn) i)
      simpa using hh
    choose r hr using hc
    refine ⟨b.equivFun.symm r, fun n ↦ (hcoord (I ^ n) _ _).mpr fun i ↦ ?_⟩
    simpa only [Module.Basis.equivFun_symm_apply, Module.Basis.repr_sum_self] using hr i n

/-- A finite free module inherits adic completeness from its base ring. -/
theorem adicComplete_of_finite_free (I : Ideal R) [IsAdicComplete I R]
    [Module.Finite R M] [Module.Free R M] : IsAdicComplete I M :=
  adicComplete_of_finite_basis (Module.Free.chooseBasis R M) I

/-- Finite free algebras are complete for the ideal extended from a complete base. -/
theorem adicComplete_finite_free_algebra (I : Ideal R) [IsAdicComplete I R]
    (A : Type*) [CommRing A] [Algebra R A] [Module.Finite R A] [Module.Free R A] :
    IsAdicComplete (I.map (algebraMap R A)) A := by
  let : IsAdicComplete I A := adicComplete_of_finite_free I
  exact (IsAdicComplete.map_algebraMap_iff I A).mpr inferInstance

end ThreeAdicPlan
