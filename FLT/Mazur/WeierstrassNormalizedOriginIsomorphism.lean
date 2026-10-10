/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginIsomorphismAdmissible
public import FLT.Mazur.WeierstrassOriginIsomorphismEvaluation
public import FLT.Mazur.WeierstrassNormalizedFrameTransport

/-!
# Normalized equations are invariant under actual marked isomorphisms

An arbitrary origin-preserving scheme isomorphism carrying the three actual
normalized sections preserves the equation and the unit separation exactly.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) (e : integralCurve W ≅ integralCurve V)
  (hb : e.hom ≫ integralCurveStructure V = integralCurveStructure W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero V)

include hW hV hb hz in
/-- Normalized equations and separations agree under any actual marked scheme isomorphism. -/
theorem normalizedOriginIso_equation_eq (d k : Rˣ)
    (p : Fin 3 → Coordinate W 2 →ₐ[R] R) (q : Fin 3 → Coordinate V 2 →ₐ[R] R)
    (hp : IsNormalizedEvaluationFrame W d p) (hq : IsNormalizedEvaluationFrame V k q)
    (hm : ∀ i, Spec.map (CommRingCat.ofHom (p i).toRingHom) ≫
        integralCurveChart W 2 ≫ e.hom =
      Spec.map (CommRingCat.ofHom (q i).toRingHom) ≫ integralCurveChart V 2) :
    W = V ∧ d = k := by
  obtain ⟨C, hC, hf⟩ := originIsoCoordinateHom_exists_admissible W V hW hV e hb hz
  have he i : (p i).comp (affineVariableChangeMap V W C hC) = q i := by
    rw [← hf]
    exact originIsoCoordinateHom_evaluation W V hV e hb hz (p i) (q i) (hm i)
  obtain ⟨hc, hd⟩ := normalizedEvaluationFrame_change_eq_one W V C hC d k p q hp hq he
  exact ⟨(by simpa only [hc, one_smul] using hC.symm), hd⟩

include hW in
/-- The whole affine coordinate tuple is preserved under the actual normalized isomorphism. -/
theorem normalizedOriginIso_coordinates (d k : Rˣ)
    (p : Fin 3 → Coordinate W 2 →ₐ[R] R) (q : Fin 3 → Coordinate V 2 →ₐ[R] R)
    (hp : IsNormalizedEvaluationFrame W d p) (hq : IsNormalizedEvaluationFrame V k q)
    (hm : ∀ i, Spec.map (CommRingCat.ofHom (p i).toRingHom) ≫
        integralCurveChart W 2 ≫ e.hom =
      Spec.map (CommRingCat.ofHom (q i).toRingHom) ≫ integralCurveChart V 2) (i : Fin 3) :
    originIsoCoordinateHom W V hV e hb hz (coord V 2 i) = coord W 2 i := by
  obtain ⟨C, hC, hf⟩ := originIsoCoordinateHom_exists_admissible W V hW hV e hb hz
  have he j : (p j).comp (affineVariableChangeMap V W C hC) = q j := by
    rw [← hf]
    exact originIsoCoordinateHom_evaluation W V hV e hb hz (p j) (q j) (hm j)
  obtain ⟨rfl, _⟩ := normalizedEvaluationFrame_change_eq_one W V C hC d k p q hp hq he
  rw [hf]
  fin_cases i
  · change affineVariableChangeMap V W 1 hC (coord V 2 0) = coord W 2 0
    simp only [affineVariableChangeMap_x, WeierstrassCurve.VariableChange.one_def,
      Units.val_one, map_one, map_zero, one_pow, one_mul, add_zero]
  · change affineVariableChangeMap V W 1 hC (coord V 2 1) = coord W 2 1
    simp only [affineVariableChangeMap_y, WeierstrassCurve.VariableChange.one_def,
      Units.val_one, map_one, map_zero, one_pow, one_mul, zero_mul, add_zero]
  · change affineVariableChangeMap V W 1 hC (coord V 2 2) = coord W 2 2
    simp only [coord_self, map_one]

end FLT.Mazur.WeierstrassIntegralChart
