/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalQuotientDiagramRefinement

/-!
# Representatives retaining an actual old principal arrow

Lift the old arrow, then use its original recovery square to prove preservation
of the full ambient ideal. The same representatives retain both squares.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PrincipalQuotientProjection

universe u v

variable {R : Type u} [CommRing R] (n : ℕ)
  (I : Ideal (MvPolynomial (Fin n) R)) (a : MvPolynomial (Fin n) R) (c : Finset I)
  {Q : Type v} [CommRing Q] [Algebra R Q] (J : Ideal Q) (r : Q) (b : Finset J)

/-- Old-arrow representatives preserve the full ideal and recover both old and original arrows. -/
theorem exists_old_representatives
    (F : Target I a →ₐ[R] Target J r)
    (G : FiniteRelationLocalization.Stage I a c →ₐ[R]
      FiniteRelationLocalization.Stage J r b)
    (hG : (FiniteRelationLocalization.toQuotient R J r b).comp G =
      F.comp (FiniteRelationLocalization.toQuotient R I a c)) :
    ∃ f : MvPolynomial (Fin n) R →ₐ[R] Localization.Away r,
      (∀ p, projection (FiniteRelationModel.relations J b) r (f p) =
        G (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I c) p))) ∧
      (∀ p, projection J r (f p) = F (algebraMap _ _ (Ideal.Quotient.mk I p))) ∧
      I ≤ (J.map (algebraMap _ (Localization.Away r))).comap f.toRingHom ∧
      ∃ v : Localization.Away r,
        f a * v - 1 ∈ J.map (algebraMap _ (Localization.Away r)) := by
  obtain ⟨f, hfac, _, v, hv⟩ := exists_representatives n
    (FiniteRelationModel.relations I c) a (FiniteRelationModel.relations J b) r G
  have hfull (p) : projection J r (f p) =
      F (algebraMap _ _ (Ideal.Quotient.mk I p)) := by
    rw [← FiniteRelationLocalization.toQuotient_projection R J r b, hfac]
    have h := AlgHom.congr_fun hG
      (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I c) p))
    simpa only [AlgHom.comp_apply, FiniteRelationLocalization.toQuotient_algebraMap,
      FiniteRelationModel.toQuotient_mk] using h
  refine ⟨f, hfac, hfull, ?_, v, ?_⟩
  · intro p hp
    change f p ∈ J.map (algebraMap _ (Localization.Away r))
    rw [← ker_projection, RingHom.mem_ker, hfull]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero, map_zero]
  · exact Ideal.map_mono (FiniteRelationModel.relations_le J b) hv

end FLT.Mazur.PrincipalQuotientProjection
