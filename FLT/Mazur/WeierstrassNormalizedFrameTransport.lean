/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassNormalizedFrameUnique
public import FLT.Mazur.WeierstrassAffineVariableChangeMap

/-!
# Normalized affine evaluations remove admissible coordinate freedom

The three actual evaluations carry (0,0), (0,-d), and (-d,0). Transport
between two such frames forces the admissible change and separation uniquely.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W V : WeierstrassCurve R)

/-- A frame consists of the three specified normalized affine evaluations. -/
def IsNormalizedEvaluationFrame (d : Rˣ) (p : Fin 3 → Coordinate W 2 →ₐ[R] R) : Prop :=
  (p 0 (coord W 2 0) = 0 ∧ p 0 (coord W 2 1) = 0) ∧
  (p 1 (coord W 2 0) = 0 ∧ p 1 (coord W 2 1) = -(d : R)) ∧
  (p 2 (coord W 2 0) = -(d : R) ∧ p 2 (coord W 2 1) = 0)

/-- Transporting the full normalized frame forces an admissible change to be identity. -/
theorem normalizedEvaluationFrame_change_eq_one (C : VariableChange R) (h : C • V = W)
    (d e : Rˣ) (p : Fin 3 → Coordinate W 2 →ₐ[R] R)
    (q : Fin 3 → Coordinate V 2 →ₐ[R] R)
    (hp : IsNormalizedEvaluationFrame W d p) (hq : IsNormalizedEvaluationFrame V e q)
    (hf : ∀ i, (p i).comp (affineVariableChangeMap V W C h) = q i) : C = 1 ∧ d = e := by
  have hx (i : Fin 3) : (C.u : R) ^ 2 * p i (coord W 2 0) + C.r =
      q i (coord V 2 0) := by
    have he := DFunLike.congr_fun (hf i) (coord V 2 0)
    simpa only [AlgHom.comp_apply, affineVariableChangeMap_x, map_add, map_mul,
      map_pow, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using he
  have hy (i : Fin 3) : (C.u : R) ^ 3 * p i (coord W 2 1) +
      (C.u : R) ^ 2 * C.s * p i (coord W 2 0) + C.t = q i (coord V 2 1) := by
    have he := DFunLike.congr_fun (hf i) (coord V 2 1)
    simpa only [AlgHom.comp_apply, affineVariableChangeMap_y, map_add, map_mul,
      map_pow, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using he
  have hr : C.r = 0 := by simpa only [hp.1.1, hq.1.1, mul_zero, zero_add] using hx 0
  have ht : C.t = 0 := by
    simpa only [hp.1.1, hp.1.2, hq.1.2, mul_zero, zero_add] using hy 0
  have hxx : (C.u : R) ^ 2 * -(d : R) + C.r = -(e : R) := by
    simpa only [hp.2.2.1, hq.2.2.1] using hx 2
  have hyy : (C.u : R) ^ 3 * -(d : R) + C.t = -(e : R) := by
    simpa only [hp.2.1.1, hp.2.1.2, hq.2.1.2, mul_zero, add_zero] using hy 1
  have hss : (C.u : R) ^ 2 * C.s * -(d : R) + C.t = 0 := by
    simpa only [hp.2.2.1, hp.2.2.2, hq.2.2.2, mul_zero, zero_add] using hy 2
  obtain ⟨hc, hd⟩ := WeierstrassNormalizedFrameUnique.change_eq_one C e d hr ht hxx hyy hss
  exact ⟨hc, hd.symm⟩

end FLT.Mazur.WeierstrassIntegralChart
