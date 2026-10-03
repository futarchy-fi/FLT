/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletionScalars

/-!
# Completion of a principal quotient

Exactness of completion over a Noetherian ring identifies the kernel of
the completed quotient map with the principal ideal of the completed relation.
-/

open AdicCompletion
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.AdicCompletionPrincipal
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (I : Ideal R) (r : R)

theorem kernel (hr : Function.Injective (fun x : R ↦ r * x)) :
    RingHom.ker (AdicCompletionScalars.algebraMapCompletion
      (S := R ⧸ Ideal.span {r}) I).toRingHom =
      Ideal.span {of I R r} := by
  let f : R →ₗ[R] R := r • LinearMap.id
  let g := Algebra.linearMap R (R ⧸ Ideal.span {r})
  have hf : Function.Injective f := hr
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective
  have hfg : Function.Exact f g := by
    intro x
    change Ideal.Quotient.mk (Ideal.span {r}) x = 0 ↔ ∃ y, r * y = x
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    simp only [dvd_def, eq_comm]
  have he := map_exact (I := I) hf hfg hg
  have hm (x : AdicCompletion I R) : map I f x = of I R r * x := by
    simp only [f, map_smul, map_id, LinearMap.smul_apply, LinearMap.id_apply]
    exact (Algebra.smul_def r x)
  ext x
  change AdicCompletionScalars.equivalence I (map I g x) = 0 ↔ _
  rw [map_eq_zero_iff _ (AdicCompletionScalars.equivalence I).injective, he]
  simp only [Set.mem_range, hm, Ideal.mem_span_singleton, dvd_def, eq_comm]

/-- Completion commutes with a quotient by a non-zero-divisor. -/
def equivalence (hr : Function.Injective (fun x : R ↦ r * x)) :
    (AdicCompletion I R ⧸ Ideal.span {of I R r}) ≃ₐ[R]
      AdicCompletion (I.map (Ideal.Quotient.mk (Ideal.span {r})))
        (R ⧸ Ideal.span {r}) :=
  (Ideal.quotientEquivAlgOfEq R (kernel I r hr).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (AdicCompletionScalars.algebraMapCompletion_surjective I
        (Ideal.Quotient.mk_surjective (I := Ideal.span {r}))))
end FLT.Mazur.AdicCompletionPrincipal
