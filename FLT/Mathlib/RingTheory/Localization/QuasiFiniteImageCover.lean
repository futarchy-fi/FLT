/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.KrullDimension.QuasiFiniteBaseChangeFibre
public import FLT.Mathlib.RingTheory.Localization.FiniteImagePrincipalCover
public import FLT.Mathlib.RingTheory.Localization.ZeroDimensionalFibreNeighbourhood

/-! # A finite cover by quasi-finite neighbourhoods of a coefficient-stage spectrum image -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [FiniteType R A] [QuasiFinite S (S ⊗[R] A)]

/-- A quasi-finite final base change is covered by finitely many principal opens from
the coefficient stage, each already quasi-finite over the stage base. -/
theorem exists_finite_quasiFinite_image_cover :
    ∃ (t : Finset (S ⊗[R] A)) (a : t → A),
      (∀ i, QuasiFinite R (Localization.Away (a i))) ∧
      Ideal.span (Set.range fun i ↦
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) (a i)) = ⊤ := by
  let φ := (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom
  have h (Q : Ideal (S ⊗[R] A)) [Q.IsPrime] :
      ∃ a : A, φ a ∉ Q ∧ QuasiFinite R (Localization.Away a) := by
    let q := Q.comap φ
    let p := Q.under S
    have hp : p.comap (algebraMap R S) = q.under R := by
      simp only [p, q, Ideal.under, Ideal.comap_comap]
      congr 1
      ext r
      simp [φ]
    have hd := fibre_dimension_zero_of_quasiFinite_baseChange (R := R) (A := A) p
    apply exists_principal_of_fibre_dimension_zero (R := R) ⟨q, inferInstance⟩
    have transfer (p' : Ideal R) [p'.IsPrime] (he : p' = q.under R)
        (hh : ringKrullDim (p'.Fiber A) ≤ 0) :
        ringKrullDim ((q.under R).Fiber A) ≤ 0 := by
      subst p'
      exact hh
    exact transfer _ hp hd
  obtain ⟨t, a, ha, _, hspan⟩ := φ.exists_finite_image_principal_cover
    (fun a ↦ QuasiFinite R (Localization.Away a)) h
  exact ⟨t, a, ha, hspan⟩

end Algebra
