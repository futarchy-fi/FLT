/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteLocalizedIdealQuotient
public import Mathlib.RingTheory.Etale.QuasiFinite

/-!
# Actual ambient charts from etale finite quotient branches

Etale splitting of a quasi-finite quotient produces an idempotent finite
branch. Lift that idempotent to the coefficient-changed ambient and localize
there. The resulting full ideal quotient is finite over the new base, and
its chart contains a prime over the prescribed original support point.
-/

@[expose] public noncomputable section
open TensorProduct
universe u
namespace FLT.Mazur.FCurve
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- Lift the finite etale branch from the quotient to an actual principal ambient chart. -/
theorem exists_etale_finite_quotient_branch (I : Ideal B)
    [Algebra.FiniteType R (B ⧸ I)] [Algebra.QuasiFinite R (B ⧸ I)]
    (q : Ideal (B ⧸ I)) [q.IsPrime] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Algebra.Etale R S)
      (s : S ⊗[R] B) (P : Ideal (S ⊗[R] B)) (_ : P.IsPrime),
      P.comap (Algebra.TensorProduct.includeRight (R := R) (A := S)) =
        q.comap (Ideal.Quotient.mk I) ∧ s ∉ P ∧
      Module.Finite S (Localization.Away s ⧸
        (I.map (Algebra.TensorProduct.includeRight (R := R) (A := S))).map
          (algebraMap (S ⊗[R] B) (Localization.Away s))) := by
  let p := q.under R
  obtain ⟨S, hS, hRS, hEt, Q, hQ, hQp, e, _, Q', hQ', _, hQ'q, heQ', _, hfin, _⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q
  let T := S ⊗[R] B
  let J := I.map (Algebra.TensorProduct.includeRight (R := R) (A := S))
  let E := Algebra.TensorProduct.tensorQuotientEquiv (R := R) S B S I
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (E e)
  let P := (Q'.comap E.symm.toRingHom).comap (Ideal.Quotient.mk J)
  let _ : P.IsPrime := inferInstance
  have hP : P.comap (Algebra.TensorProduct.includeRight (R := R) (A := S)) =
      q.comap (Ideal.Quotient.mk I) := by
    ext b
    change E.symm (Ideal.Quotient.mk J (1 ⊗ₜ[R] b)) ∈ Q' ↔ Ideal.Quotient.mk I b ∈ q
    rw [Algebra.TensorProduct.tensorQuotientEquiv_symm_apply_tmul]
    exact SetLike.ext_iff.mp hQ'q (Ideal.Quotient.mk I b)
  have hsP : s ∉ P := by
    change E.symm (Ideal.Quotient.mk J s) ∉ Q'
    rw [hs, E.symm_apply_apply]
    exact heQ'
  let E' : Localization.Away e ≃ₐ[S] Localization.Away (E e) :=
    IsLocalization.algEquivOfAlgEquiv _ _ E
      (M := .powers e) (T := .powers (E e)) (by simp)
  let _ : Module.Finite S (Localization.Away (Ideal.Quotient.mk J s)) := by
    rw [hs]
    exact Module.Finite.equiv E'.toLinearEquiv
  exact ⟨S, hS, hRS, hEt, s, P, inferInstance, hP, hsP,
    finite_localized_ideal_quotient (R := S) J s⟩

end FLT.Mazur.FCurve
