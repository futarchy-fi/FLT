/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IteratedOldDenominatorRecovery
public import FLT.Mazur.SurjectivePolynomialArrowRepresentatives

/-!
# Representatives retaining actual old double-open arrows

Lift an old arrow through the literal old-coordinate projection. Its original
recovery square proves preservation of the full twice extended ambient ideal.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.IteratedQuotientProjection

universe u v

variable {R : Type u} [CommRing R] (n : ℕ)
  (I : Ideal (MvPolynomial (Fin n) R)) (a : MvPolynomial (Fin n) R) (c : Finset I)
  {Q : Type v} [CommRing Q] [Algebra R Q] (J : Ideal Q) (r : Q) (b : Finset J)
  (d : FiniteRelationLocalization.Stage J r b) (t : Set.Ici b)

/-- One lifted family retains the literal old arrow and its entire original recovery. -/
theorem exists_old_representatives
    (F : PrincipalQuotientProjection.Target I a →ₐ[R]
      FiniteRelationIterated.Quotient R J r b d)
    (G : FiniteRelationLocalization.Stage I a c →ₐ[R]
      FiniteRelationIterated.Stage R J r b d t)
    (hG : (FiniteRelationIterated.toQuotient R J r b d t).comp G =
      F.comp (FiniteRelationLocalization.toQuotient R I a c)) :
    ∃ f : MvPolynomial (Fin n) R →ₐ[R]
        Localization.Away (oldDenominatorRepresentative J r b d),
      (∀ p, oldDenominatorProjection R J r b d t (f p) =
        G (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I c) p))) ∧
      (∀ p, oldDenominatorOriginalProjection R J r b d (f p) =
        F (algebraMap _ _ (Ideal.Quotient.mk I p))) ∧
      I ≤ ((J.map (algebraMap _ (Localization.Away r))).map
        (algebraMap _ (Localization.Away (oldDenominatorRepresentative J r b d)))).comap
          f.toRingHom ∧
      ∃ v : Localization.Away (oldDenominatorRepresentative J r b d),
        f a * v - 1 ∈ (J.map (algebraMap _ (Localization.Away r))).map
          (algebraMap _ (Localization.Away (oldDenominatorRepresentative J r b d))) := by
  obtain ⟨f, hfac, _, v, hv⟩ :=
    PrincipalQuotientProjection.exists_representatives_of_surjective n
      (FiniteRelationModel.relations I c) a (oldDenominatorProjection R J r b d t)
      (oldDenominatorProjection_surjective R J r b d t) G
  have hfull (p) : oldDenominatorOriginalProjection R J r b d (f p) =
      F (algebraMap _ _ (Ideal.Quotient.mk I p)) := by
    rw [← oldDenominatorProjection_toQuotient R J r b d t, AlgHom.comp_apply, hfac]
    have h := AlgHom.congr_fun hG
      (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I c) p))
    simpa only [AlgHom.comp_apply, FiniteRelationLocalization.toQuotient_algebraMap,
      FiniteRelationModel.toQuotient_mk] using h
  refine ⟨f, hfac, hfull, ?_, v, ?_⟩
  · intro p hp
    change f p ∈ (J.map (algebraMap _ (Localization.Away r))).map
      (algebraMap _ (Localization.Away (oldDenominatorRepresentative J r b d)))
    rw [← ker_oldDenominatorOriginalProjection R J r b d, RingHom.mem_ker]
    change oldDenominatorOriginalProjection R J r b d (f p) = 0
    rw [hfull, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero, map_zero]
  · rw [ker_oldDenominatorProjection] at hv
    exact Ideal.map_mono (Ideal.map_mono (FiniteRelationModel.relations_le J t.val)) hv

end FLT.Mazur.IteratedQuotientProjection
