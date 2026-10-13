/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleTranslationBranchMaps
public import Mathlib.RingTheory.Etale.QuasiFinite

/-!
# Constructed finite translation neighborhoods at every prime

Etale splitting supplies an actual principal branch after an etale base
change. The branch is finite over that new base and retains the original
chosen translation point. Its distinguished base fiber has just one point;
this does not identify the residue field or assert fullness of a relation.
-/

@[expose] public noncomputable section
open TensorProduct CategoryTheory AlgebraicGeometry
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace FLT.Mazur.EtaleTranslationBranch
universe u
set_option backward.isDefEq.respectTransparency false
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- A quasi-finite translation point has a finite branch with a single distinguished base fiber. -/
theorem exists_finite_branch [Algebra.FiniteType R B] [Algebra.QuasiFinite R B]
    (q : PrimeSpectrum B) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Algebra.Etale R S)
      (e : S ⊗[R] B), IsIdempotentElem e ∧ Module.Finite S (Localization.Away e) ∧
      ∃ x : source e, toOriginal e x = q ∧
        ∀ y : source e, toBase e y = toBase e x → y = x := by
  let p := q.asIdeal.under R
  obtain ⟨S, hS, hRS, hEt, P, hP, hPp, e, he, Q, hQ, hQP, hQq, heQ, _, hfin, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q.asIdeal
  obtain ⟨x, hx⟩ := exists_branch_point e Q heQ
  have hxQ : x.asIdeal.comap (algebraMap (S ⊗[R] B) (Localization.Away e)) = Q :=
    congrArg PrimeSpectrum.asIdeal hx
  have hxP : x.asIdeal.comap (algebraMap S (Localization.Away e)) = P := by
    rw [IsScalarTower.algebraMap_eq S (S ⊗[R] B) (Localization.Away e),
      ← Ideal.comap_comap, hxQ]
    exact (Q.over_def P).symm
  refine ⟨S, hS, hRS, hEt, e, he, hfin, x, ?_, ?_⟩
  · apply PrimeSpectrum.ext
    change x.asIdeal.comap (algebraMap B (Localization.Away e)) = q.asIdeal
    rw [IsScalarTower.algebraMap_eq B (S ⊗[R] B) (Localization.Away e),
      ← Ideal.comap_comap, hxQ]
    exact hQq
  · intro y hy
    let Q' := y.asIdeal.comap (algebraMap (S ⊗[R] B) (Localization.Away e))
    have hyP : y.asIdeal.comap (algebraMap S (Localization.Away e)) = P :=
      (congrArg PrimeSpectrum.asIdeal hy).trans hxP
    let _ : Q'.LiesOver P := ⟨by
      change P = Q'.comap (algebraMap S (S ⊗[R] B))
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
      exact hyP.symm⟩
    have heQ' : e ∉ Q' := by
      intro h
      exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem y.asIdeal h
        (IsLocalization.Away.algebraMap_isUnit e))
    have hyQ : Q' = Q := huniq Q' inferInstance inferInstance heQ'
    apply (inclusion e).injective
    exact (PrimeSpectrum.ext hyQ).trans hx.symm

/-- For etale translations the constructed finite branch is etale on both sides. -/
theorem exists_finite_etale_branch [Algebra.Etale R B] (q : PrimeSpectrum B) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Algebra.Etale R S)
      (e : S ⊗[R] B), IsIdempotentElem e ∧ IsFinite (toBase e) ∧
      Etale (toBase e) ∧ Etale (toOriginal e) ∧
      ∃ x : source e, toOriginal e x = q ∧
        ∀ y : source e, toBase e y = toBase e x → y = x := by
  obtain ⟨S, hS, hRS, hEt, e, he, hfin, x, hx, huniq⟩ :=
    exists_finite_branch (R := R) q
  exact ⟨S, hS, hRS, hEt, e, he, inferInstance, inferInstance, inferInstance, x, hx, huniq⟩

end FLT.Mazur.EtaleTranslationBranch
