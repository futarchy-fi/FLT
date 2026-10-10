/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberBranches
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Scheme-theoretic ideals of the three oriented fiber branches

The polynomial maps have exactly the principal ideals given by the original
incidence and tangent factors. The proofs retain the full fiber algebra.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassModificationX

variable {R : Type*} [CommRing R] (a : R)

/-- The central branch sets the incidence ratio to zero. -/
@[simp] theorem fiberCentralLine_t : fiberCentralLine a (fiberT a 0) = 0 :=
  fiberEvaluation_t _ _ _ _ _

/-- The first tangent branch has slope zero. -/
@[simp] theorem fiberFirstLine_v : fiberFirstLine a (fiberV a 0) = 0 :=
  fiberEvaluation_v _ _ _ _ _

/-- The second tangent branch has the original negative tangent slope. -/
@[simp] theorem fiberSecondLine_v : fiberSecondLine a (fiberV a 0) = -C a :=
  fiberEvaluation_v _ _ _ _ _

/-- A section modulo an ideal detects the kernel without any reducedness hypothesis. -/
theorem fiber_ker_eq_of_section {S : Type*} [CommRing S] [Algebra R S]
    (f : FiberCoordinate a 0 →ₐ[R] S) (I : Ideal (FiberCoordinate a 0))
    (hI : I ≤ RingHom.ker f.toRingHom) (g : S →ₐ[R] FiberCoordinate a 0 ⧸ I)
    (ht : g (f (fiberT a 0)) = Ideal.Quotient.mk I (fiberT a 0))
    (hv : g (f (fiberV a 0)) = Ideal.Quotient.mk I (fiberV a 0)) :
    RingHom.ker f.toRingHom = I := by
  have he : g.comp f = Ideal.Quotient.mkₐ R I := fiber_hom_ext _ _ _ _ ht hv
  refine le_antisymm ?_ hI
  intro z hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hz' : f z = 0 := hz
  have := DFunLike.congr_fun he z
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hz', map_zero] using this.symm

/-- The central line is cut out scheme-theoretically by the incidence ratio. -/
theorem fiberCentralLine_ker : RingHom.ker (fiberCentralLine a).toRingHom =
    Ideal.span {fiberT a 0} := by
  let I : Ideal (FiberCoordinate a 0) := Ideal.span {fiberT a 0}
  have ht : Ideal.Quotient.mk I (fiberT a 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  refine fiber_ker_eq_of_section a (fiberCentralLine a) I
    (Ideal.span_le.mpr ?_) (aeval (Ideal.Quotient.mk I (fiberV a 0))) ?_ ?_
  · intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact fiberCentralLine_t a
  · simp only [fiberCentralLine_t, map_zero, ht]
  · simp only [fiberCentralLine_v, aeval_X]

/-- The first tangent line is cut out scheme-theoretically by the original slope. -/
theorem fiberFirstLine_ker : RingHom.ker (fiberFirstLine a).toRingHom =
    Ideal.span {fiberV a 0} := by
  let I : Ideal (FiberCoordinate a 0) := Ideal.span {fiberV a 0}
  have hv : Ideal.Quotient.mk I (fiberV a 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  refine fiber_ker_eq_of_section a (fiberFirstLine a) I
    (Ideal.span_le.mpr ?_) (aeval (Ideal.Quotient.mk I (fiberT a 0))) ?_ ?_
  · intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact fiberFirstLine_v a
  · simp only [fiberFirstLine_t, aeval_X]
  · simp only [fiberFirstLine_v, map_zero, hv]

/-- The second tangent line is cut out by the original translated slope. -/
theorem fiberSecondLine_ker : RingHom.ker (fiberSecondLine a).toRingHom =
    Ideal.span {fiberV a 0 + algebraMap R _ a} := by
  let I : Ideal (FiberCoordinate a 0) :=
    Ideal.span {fiberV a 0 + algebraMap R _ a}
  have hv : Ideal.Quotient.mk I (fiberV a 0) + algebraMap R _ a = 0 := by
    simpa only [map_add, Ideal.Quotient.mk_algebraMap] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton (fiberV a 0 + algebraMap R _ a))) :
        Ideal.Quotient.mk I (fiberV a 0 + algebraMap R _ a) = 0)
  refine fiber_ker_eq_of_section a (fiberSecondLine a) I
    (Ideal.span_le.mpr ?_) (aeval (Ideal.Quotient.mk I (fiberT a 0))) ?_ ?_
  · intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    change fiberSecondLine a _ = 0
    simp only [map_add, fiberSecondLine_v, AlgHom.commutes, algebraMap_eq, neg_add_cancel]
  · simp only [fiberSecondLine_t, aeval_X]
  · simpa only [fiberSecondLine_v, map_neg, aeval_C] using (eq_neg_of_add_eq_zero_left hv).symm

end FLT.Mazur.WeierstrassModificationX
