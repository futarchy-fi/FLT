/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOriginalSmoothMarking
public import FLT.Mazur.PolygonSinglePointHZero

/-!
# Pole-space dimensions for original smooth points on any split polygon

The canonical normalization calculation applies to the actual original point
ideal. Neither the original group law nor its identity is replaced by the
split model's group law or identity.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonOriginalPointPowers
open FCurve PolygonPinching PolygonSinglePointLineNormalization
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] (E : GeneralizedEllipticCurve (Spec (.of K)))
  (n : ℕ) [NeZero n] (hn : 0 < n)
  (p : components K n ⟶ E.curve) (q : nodes K n ⟶ E.curve)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

include h in
/-- All positive powers of any original smooth marking have exactly the expected H0. -/
theorem finrank (s : 𝟙_ (Over (Spec (.of K))) ⟶ E.group) (m : ℕ) (hm : 0 < m) :
    Module.finrank K (ModuleScalarH E.curve.hom (E.smoothMarkingPower s m) 0) = m := by
  obtain ⟨a, i, hs⟩ := PolygonOriginalSmoothMarking.exists_sectionMap E n hn p q h s
  let e : E.smoothMarkingPower s m ≅ pointPower K n hn p q h a i m := by
    simpa only [GeneralizedEllipticCurve.smoothMarkingPower, hs, pointLine] using
      pointPowerIso K n hn p q h a i m
  exact ((moduleScalarHFunctor E.curve.hom 0).mapIso e).toLinearEquiv.finrank_eq.trans
    (PolygonSinglePointHZero.finrank K n hn p q h a i m hm)

/-- The classification alone supplies the pinching needed for the pole-space calculation. -/
theorem finrank_of_isNeronPolygon (hc : IsNeronPolygon E.curve)
    (s : 𝟙_ (Over (Spec (.of K))) ⟶ E.group) (m : ℕ) (hm : 0 < m) :
    Module.finrank K (ModuleScalarH E.curve.hom (E.smoothMarkingPower s m) 0) = m := by
  obtain ⟨n, hn, p, q, h⟩ := hc
  let _ : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact finrank E n hn p q h s m hm

end FLT.Mazur.PolygonOriginalPointPowers
