/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassNormalizedOriginIsomorphism
public import FLT.Mazur.WeierstrassAffineMorphismExt

/-!
# The entire normalized proper comparison is equality transport

The normalized frame determines the whole proper map, including the section
at infinity and nilpotent directions, by schematic density of the affine chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) (e : integralCurve W ≅ integralCurve V)
  (hb : e.hom ≫ integralCurveStructure V = integralCurveStructure W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero V)
  (d k : Rˣ) (p : Fin 3 → Coordinate W 2 →ₐ[R] R)
  (q : Fin 3 → Coordinate V 2 →ₐ[R] R)
  (hp : IsNormalizedEvaluationFrame W d p) (hq : IsNormalizedEvaluationFrame V k q)
  (hm : ∀ i, Spec.map (CommRingCat.ofHom (p i).toRingHom) ≫
      integralCurveChart W 2 ≫ e.hom =
    Spec.map (CommRingCat.ofHom (q i).toRingHom) ≫ integralCurveChart V 2)

include hW hV hb hz hp hq hm in
/-- Preserving an actual normalized frame determines the full proper comparison uniquely. -/
theorem normalizedOriginIso_hom_eq (h : W = V) :
    e.hom = eqToHom (congrArg integralCurve h) := by
  subst V
  have hc : originIsoCoordinateHom W W hV e hb hz = AlgHom.id R (Coordinate W 2) := by
    apply hom_ext
    intro i
    exact normalizedOriginIso_coordinates W W hW hV e hb hz d k p q hp hq hm i
  apply integralCurve_hom_ext_affine W (integralCurveStructure W)
  · simpa only [eqToHom_refl, Category.id_comp] using hb
  · rw [← originIsoAffineHom_inclusion W W hV e hb hz,
      ← originIsoCoordinateHom_spec W W hV e hb hz, hc]
    simp only [AlgHom.toRingHom_eq_coe, eqToHom_refl]
    change Spec.map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
    rw [Spec.map_id, Category.id_comp, Category.comp_id]

include hW hV hb hz hp hq hm in
/-- The normalized frame yields both equation equality and the actual proper equality map. -/
theorem normalizedOriginIso_eq_transport :
    ∃ h : W = V, e.hom = eqToHom (congrArg integralCurve h) := by
  obtain ⟨h, _⟩ := normalizedOriginIso_equation_eq W V hW hV e hb hz d k p q hp hq hm
  exact ⟨h, normalizedOriginIso_hom_eq W V hW hV e hb hz d k p q hp hq hm h⟩

end FLT.Mazur.WeierstrassIntegralChart
