/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# Multivariable relations from differential annihilation

For any generating family of an algebra whose Kähler differentials are killed
by `a`, the relation ideal contains polynomials whose evaluated gradients are
`a` times the coordinate vectors. This is the multivariable counterpart of a
polynomial Bézout identity. It does not require a power basis, a square
presentation, or freeness of the conormal module.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace Algebra.Generators

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- An annihilator of Kähler differentials multiplies every vector in the
ambient cotangent space into the image of the relation differential. -/
theorem exists_cotangentComplex_eq_smul (P : Generators R S ι) (a : R)
    (ha : ∀ ω : KaehlerDifferential R S, a • ω = 0)
    (v : P.toExtension.CotangentSpace) :
    ∃ z : P.toExtension.Cotangent,
      P.toExtension.cotangentComplex z = algebraMap R S a • v := by
  apply (P.toExtension.exact_cotangentComplex_toKaehler _).mp
  rw [map_smul, algebraMap_smul]
  exact ha _

/-- For each coordinate, there is a relation whose gradient in the quotient
is the corresponding coordinate vector multiplied by the differential annihilator. -/
theorem exists_relation_pderiv_eq [DecidableEq ι] (P : Generators R S ι) (a : R)
    (ha : ∀ ω : KaehlerDifferential R S, a • ω = 0) (i : ι) :
    ∃ f : MvPolynomial ι R, f ∈ P.ker ∧
      ∀ j, aeval P.val (pderiv j f) = if i = j then algebraMap R S a else 0 := by
  classical
  obtain ⟨z, hz⟩ := P.exists_cotangentComplex_eq_smul a ha (P.cotangentSpaceBasis i)
  obtain ⟨f, rfl⟩ := Extension.Cotangent.mk_surjective z
  refine ⟨f.1, f.property, fun j ↦ ?_⟩
  have h := congrArg (fun v ↦ P.cotangentSpaceBasis.repr v j) hz
  simpa only [Extension.cotangentComplex_mk, P.cotangentSpaceBasis_repr_one_tmul,
    map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero] using h

/-- An approximate point annihilates every defining relation modulo the
approximation ideal, for any lifts of its generator coordinates. -/
theorem aeval_mem_ideal_of_mem_ker (P : Generators R S ι)
    {T : Type*} [CommRing T] [Algebra R T] (I : Ideal T)
    (u : S →ₐ[R] T ⧸ I) (x : ι → T)
    (hx : ∀ i, Ideal.Quotient.mk I (x i) = u (P.val i))
    {f : MvPolynomial ι R} (hf : f ∈ P.ker) : aeval x f ∈ I := by
  have he : (Ideal.Quotient.mkₐ R I).comp (aeval x) = u.comp (aeval P.val) := by
    ext i
    simpa only [AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk] using hx i
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change ((Ideal.Quotient.mkₐ R I).comp (aeval x)) f = 0
  rw [he, AlgHom.comp_apply, P.aeval_val_eq_zero hf, map_zero]

/-- Differential annihilation supplies as many relations as coordinates,
with Jacobian congruent to the scalar matrix at every approximate point.
The selected relations need not generate the entire relation ideal. -/
theorem exists_relations_approximate_jacobian [DecidableEq ι]
    (P : Generators R S ι) (a : R)
    (ha : ∀ ω : KaehlerDifferential R S, a • ω = 0)
    {T : Type*} [CommRing T] [Algebra R T] (I : Ideal T)
    (u : S →ₐ[R] T ⧸ I) (x : ι → T)
    (hx : ∀ i, Ideal.Quotient.mk I (x i) = u (P.val i)) :
    ∃ f : ι → MvPolynomial ι R,
      (∀ i, f i ∈ P.ker) ∧ (∀ i, aeval x (f i) ∈ I) ∧
      ∀ i j, aeval x (pderiv j (f i)) -
        (if i = j then algebraMap R T a else 0) ∈ I := by
  classical
  choose f hf hdf using P.exists_relation_pderiv_eq a ha
  refine ⟨f, hf, fun i ↦ P.aeval_mem_ideal_of_mem_ker I u x hx (hf i), ?_⟩
  intro i j
  have hker : pderiv j (f i) - C (if i = j then a else 0) ∈ P.ker := by
    rw [P.ker_eq_ker_aeval_val, RingHom.mem_ker, map_sub, aeval_C, hdf]
    split_ifs <;> simp
  have hh := P.aeval_mem_ideal_of_mem_ker I u x hx hker
  simpa only [map_sub, aeval_C, apply_ite, map_zero] using hh

end Algebra.Generators
