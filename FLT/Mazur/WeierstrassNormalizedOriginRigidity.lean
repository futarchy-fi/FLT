/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassNormalizedOriginIsomorphism
public import FLT.Mazur.WeierstrassVariableChangeIdentity

/-!
# Rigidity of the entire normalized proper cubic

A marked normalized isomorphism is equality transport on the whole proper
scheme. This controls arbitrary sections, including those outside an affine chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) (e : integralCurve W ≅ integralCurve V)
  (hb : e.hom ≫ integralCurveStructure V = integralCurveStructure W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero V)

include hW hV hb hz in
/-- A normalized marked isomorphism is equality transport on the entire proper cubic. -/
theorem normalizedOriginIso_eq_transport (d k : Rˣ)
    (p : Fin 3 → Coordinate W 2 →ₐ[R] R) (q : Fin 3 → Coordinate V 2 →ₐ[R] R)
    (hp : IsNormalizedEvaluationFrame W d p) (hq : IsNormalizedEvaluationFrame V k q)
    (hm : ∀ i, Spec.map (CommRingCat.ofHom (p i).toRingHom) ≫
        integralCurveChart W 2 ≫ e.hom =
      Spec.map (CommRingCat.ofHom (q i).toRingHom) ≫ integralCurveChart V 2) :
    ∃ h : W = V, e = eqToIso (congrArg integralCurve h) := by
  obtain ⟨C, hC, hf⟩ := originIsoCoordinateHom_exists_admissible W V hW hV e hb hz
  have he i : (p i).comp (affineVariableChangeMap V W C hC) = q i := by
    rw [← hf]
    exact originIsoCoordinateHom_evaluation W V hV e hb hz (p i) (q i) (hm i)
  obtain ⟨hc, _⟩ := normalizedEvaluationFrame_change_eq_one W V C hC d k p q hp hq he
  have h : W = V := by simpa only [hc, one_smul] using hC.symm
  refine ⟨h, ?_⟩
  have hi := originIso_eq_integralVariableChange W V hV e hb hz C hC hf
  subst V
  subst C
  exact hi.trans (integralVariableChangeIso_one W)

include hW hV hb hz in
/-- Every normalized origin- and frame-preserving automorphism is the identity. -/
theorem normalizedOriginIso_hom_eq_transport (d k : Rˣ)
    (p : Fin 3 → Coordinate W 2 →ₐ[R] R) (q : Fin 3 → Coordinate V 2 →ₐ[R] R)
    (hp : IsNormalizedEvaluationFrame W d p) (hq : IsNormalizedEvaluationFrame V k q)
    (hm : ∀ i, Spec.map (CommRingCat.ofHom (p i).toRingHom) ≫
        integralCurveChart W 2 ≫ e.hom =
      Spec.map (CommRingCat.ofHom (q i).toRingHom) ≫ integralCurveChart V 2)
    (h : W = V) : e.hom = eqToHom (congrArg integralCurve h) := by
  obtain ⟨_, he⟩ := normalizedOriginIso_eq_transport W V hW hV e hb hz d k p q hp hq hm
  exact congrArg Iso.hom he

end FLT.Mazur.WeierstrassIntegralChart
