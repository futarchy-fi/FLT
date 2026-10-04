/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Reduction of the integral dual of a free module, preserving evaluation -/

@[expose] public noncomputable section
namespace Module
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (a : R)

/-- Reduce the values of an integral functional in the specified principal quotient. -/
def dualReduction : Dual R M →ₗ[R] (M →ₗ[R] R ⧸ Ideal.span {a}) where
  toFun f := (Ideal.Quotient.mkₐ R (Ideal.span {a})).toLinearMap.comp f
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]

variable [Free R M]

/-- Freeness lifts every quotient-valued functional to an integral one. -/
theorem dualReduction_surjective : Function.Surjective (dualReduction (M := M) a) := by
  intro f
  exact projective_lifting_property _ f Ideal.Quotient.mk_surjective

/-- The kernel consists of precisely the corresponding multiples in the integral dual. -/
theorem dualReduction_ker : LinearMap.ker (dualReduction (M := M) a) =
    LinearMap.range (a • (LinearMap.id : Dual R M →ₗ[R] _)) := by
  ext f
  constructor
  · intro hf
    let b := Free.chooseBasis R M
    have h (i : Free.ChooseBasisIndex R M) : ∃ c : R, a * c = f (b i) := by
      have hz := LinearMap.congr_fun hf (b i)
      have hm : f (b i) ∈ Ideal.span {a} := Ideal.Quotient.eq_zero_iff_mem.mp hz
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hm
      exact ⟨c, hc.symm⟩
    choose c hc using h
    refine ⟨b.constr R c, ?_⟩
    apply b.ext
    intro i
    simpa only [LinearMap.smul_apply, LinearMap.id_apply, Basis.constr_basis, smul_eq_mul]
      using hc i
  · rintro ⟨g, rfl⟩
    apply LinearMap.ext
    intro x
    change Ideal.Quotient.mk _ (a * g x) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr ⟨g x, rfl⟩

/-- The dual reduced modulo a is exactly all quotient-valued functionals. -/
def dualReductionEquiv :
    (Dual R M ⧸ LinearMap.range (a • (LinearMap.id : Dual R M →ₗ[R] _))) ≃ₗ[R]
      (M →ₗ[R] R ⧸ Ideal.span {a}) :=
  (Submodule.quotEquivOfEq _ _ (dualReduction_ker (M := M) a).symm).trans
    ((dualReduction a).quotKerEquivOfSurjective (dualReduction_surjective a))

/-- The equivalence keeps the original integral evaluation pairing. -/
theorem dualReductionEquiv_mk (f : Dual R M) (x : M) :
    dualReductionEquiv a (Submodule.Quotient.mk f) x = Ideal.Quotient.mk _ (f x) := rfl

end Module
