/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalQuotientAlgebra
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial and inverse representatives of original principal-open arrows

Every original algebra arrow supplies polynomial generator images in the
unquotiented target localization and a representative of the denominator's
inverse. All preservation and inverse equations follow in the original ideal.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PrincipalQuotientProjection

universe u v

variable {R : Type u} [CommRing R] (n : ℕ)
  (I : Ideal (MvPolynomial (Fin n) R)) (a : MvPolynomial (Fin n) R)
  {Q : Type v} [CommRing Q] [Algebra R Q] (J : Ideal Q) (r : Q)

/-- Original principal arrows have polynomial and inverse representatives with full recovery. -/
theorem exists_representatives (F : Target I a →ₐ[R] Target J r) :
    ∃ f : MvPolynomial (Fin n) R →ₐ[R] Localization.Away r,
      (∀ p, projection J r (f p) =
        F (algebraMap _ (Target I a) (Ideal.Quotient.mk I p))) ∧
      I ≤ (J.map (algebraMap Q (Localization.Away r))).comap f.toRingHom ∧
      ∃ v : Localization.Away r,
        f a * v - 1 ∈ J.map (algebraMap Q (Localization.Away r)) := by
  let g : MvPolynomial (Fin n) R →ₐ[R] Target I a :=
    (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R ⧸ I) (Target I a)).comp
      (Ideal.Quotient.mkₐ R I)
  choose y hy using fun k : Fin n ↦
    projection_surjective J r (F (g (MvPolynomial.X k)))
  let f : MvPolynomial (Fin n) R →ₐ[R] Localization.Away r := MvPolynomial.aeval y
  have hfg : (projectionAlgHom R J r).comp f = F.comp g := by
    apply MvPolynomial.algHom_ext
    intro k
    change projection J r (MvPolynomial.aeval y (MvPolynomial.X k)) = _
    rw [MvPolynomial.aeval_X]
    exact hy k
  have hfac (p) : projection J r (f p) =
      F (algebraMap _ (Target I a) (Ideal.Quotient.mk I p)) :=
    AlgHom.congr_fun hfg p
  refine ⟨f, hfac, ?_, ?_⟩
  · intro p hp
    change f p ∈ J.map (algebraMap Q (Localization.Away r))
    rw [← ker_projection, RingHom.mem_ker, hfac]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero, map_zero]
  · obtain ⟨v, hv⟩ := projection_surjective J r
      (F (IsLocalization.Away.invSelf (S := Target I a) (Ideal.Quotient.mk I a)))
    refine ⟨v, ?_⟩
    rw [← ker_projection, RingHom.mem_ker, map_sub, map_mul, map_one, hfac, hv]
    rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one, sub_self]

end FLT.Mazur.PrincipalQuotientProjection
