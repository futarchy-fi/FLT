/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IteratedQuotientAlgebra
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Representatives of arrows into original iterated principal opens

Every original algebra arrow supplies polynomial generator images in the
unquotiented target localization and a representative of the denominator's
inverse. All preservation and inverse equations follow in the original ideal.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.IteratedQuotientProjection

universe u v

variable {R : Type u} [CommRing R] (n : ℕ)
  (I : Ideal (MvPolynomial (Fin n) R)) (a : MvPolynomial (Fin n) R)
  {Q : Type v} [CommRing Q] [Algebra R Q] (J : Ideal Q) (r : Q)
  (s : Localization.Away r)

/-- Original principal arrows have polynomial and inverse representatives with full recovery. -/
theorem exists_representatives (F : PrincipalQuotientProjection.Target I a →ₐ[R] Target J r s) :
    ∃ f : MvPolynomial (Fin n) R →ₐ[R] Localization.Away s,
      (∀ p, projection J r s (f p) =
        F (algebraMap _ (PrincipalQuotientProjection.Target I a) (Ideal.Quotient.mk I p))) ∧
      I ≤ ((J.map (algebraMap Q (Localization.Away r))).map
        (algebraMap _ (Localization.Away s))).comap f.toRingHom ∧
      ∃ v : Localization.Away s,
        f a * v - 1 ∈ (J.map (algebraMap Q (Localization.Away r))).map
          (algebraMap _ (Localization.Away s)) := by
  let g : MvPolynomial (Fin n) R →ₐ[R] PrincipalQuotientProjection.Target I a :=
    (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R ⧸ I)
      (PrincipalQuotientProjection.Target I a)).comp
      (Ideal.Quotient.mkₐ R I)
  choose y hy using fun k : Fin n ↦
    projection_surjective J r s (F (g (MvPolynomial.X k)))
  let f : MvPolynomial (Fin n) R →ₐ[R] Localization.Away s := MvPolynomial.aeval y
  have hfg : (projectionAlgHom J r s R).comp f = F.comp g := by
    apply MvPolynomial.algHom_ext
    intro k
    change projection J r s (MvPolynomial.aeval y (MvPolynomial.X k)) = _
    rw [MvPolynomial.aeval_X]
    exact hy k
  have hfac (p) : projection J r s (f p) =
      F (algebraMap _ (PrincipalQuotientProjection.Target I a) (Ideal.Quotient.mk I p)) :=
    AlgHom.congr_fun hfg p
  refine ⟨f, hfac, ?_, ?_⟩
  · intro p hp
    change f p ∈ (J.map (algebraMap Q (Localization.Away r))).map
          (algebraMap _ (Localization.Away s))
    rw [← ker_projection, RingHom.mem_ker, hfac]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero, map_zero]
  · obtain ⟨v, hv⟩ := projection_surjective J r s
      (F (IsLocalization.Away.invSelf (S := PrincipalQuotientProjection.Target I a)
        (Ideal.Quotient.mk I a)))
    refine ⟨v, ?_⟩
    rw [← ker_projection, RingHom.mem_ker, map_sub, map_mul, map_one, hfac, hv]
    rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one, sub_self]

end FLT.Mazur.IteratedQuotientProjection
