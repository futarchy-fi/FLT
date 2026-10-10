/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassTripleFullFiveCharts

/-!
# Associativity on the entire integral Weierstrass curve

Every actual full-cover member has five regular chart presentations and the
two original final output charts. Injective localization proves equality on
its affine opens, and the actual triple cover then gives global associativity.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Associativity on every flat affine restriction of an actual full-cover member. -/
theorem integralCurveTripleFull_assoc_onSpec (i : (integralCurveTripleFullCover W hΔ).I₀)
    {S : Type u} [CommRing S] (f : Spec (.of S) ⟶ (integralCurveTripleFullCover W hΔ).X i)
    [Flat f] : (f ≫ (integralCurveTripleFullCover W hΔ).f i) ≫
        integralCurveTripleAddLeft W hΔ =
      (f ≫ (integralCurveTripleFullCover W hΔ).f i) ≫ integralCurveTripleAddRight W hΔ := by
  apply integralCurveTripleAdd_of_fiveRegularSections W hΔ _
    (tripleFullFiveChart W hΔ i) (fun n => f ≫ tripleFullFiveSpec W hΔ i n)
    (fun n => by rw [Category.assoc, tripleFullFiveSpec_global, tripleFivePoint_comp])
    (tripleFullFiveSpec_z_regular W hΔ i f)
    (integralCurveAdditionOutput W hΔ i.1.1) (integralCurveAdditionOutput W hΔ i.1.2)
    (f ≫ integralCurveTripleFullOuter W hΔ i ≫ integralCurveTripleLeftDomain W hΔ i.1 ≫
      integralCurveAdditionSpec W hΔ i.1.1)
    (f ≫ integralCurveTripleFullOuter W hΔ i ≫ integralCurveTripleRightDomain W hΔ i.1 ≫
      integralCurveAdditionSpec W hΔ i.1.2)
  · simp only [Category.assoc, integralCurveAdditionSpec_local,
      integralCurveTripleFull_outerLeft]
  · simp only [Category.assoc, integralCurveAdditionSpec_local,
      integralCurveTripleFull_outerRight]

/-- The two genuine iterated sums agree on every member of the full triple cover. -/
theorem integralCurveTripleFull_assoc (i : (integralCurveTripleFullCover W hΔ).I₀) :
    (integralCurveTripleFullCover W hΔ).f i ≫ integralCurveTripleAddLeft W hΔ =
      (integralCurveTripleFullCover W hΔ).f i ≫ integralCurveTripleAddRight W hΔ := by
  apply Scheme.Cover.hom_ext ((integralCurveTripleFullCover W hΔ).X i).affineCover
  intro a
  simpa only [Category.assoc] using integralCurveTripleFull_assoc_onSpec W hΔ i
    (((integralCurveTripleFullCover W hΔ).X i).affineCover.f a)

/-- Global associativity of the constructed addition over any ring with unit discriminant. -/
theorem integralCurveAddition_assoc :
    integralCurveTripleAddLeft W hΔ = integralCurveTripleAddRight W hΔ :=
  (integralCurveTripleFullCover W hΔ).hom_ext _ _ (integralCurveTripleFull_assoc W hΔ)

end FLT.Mazur.WeierstrassIntegralChart
