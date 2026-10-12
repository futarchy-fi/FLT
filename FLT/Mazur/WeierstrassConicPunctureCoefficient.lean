/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassConicCoefficientMap
public import FLT.Mazur.WeierstrassSuccessiveXConicPuncturedParameters
public import FLT.Mazur.WeierstrassSplitNodalLaurentCoefficient

/-!
# Both original signed conic parameters commute with coefficients

The full Laurent parameter is unchanged. The second branch preserves both
its negative incidence scale and its original negative slope.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassSuccessiveX WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)
  (W : WeierstrassCurve S) (V : WeierstrassCurve T)
  (c : S) (d : T) (ha : f W.a₁ = V.a₁) (hc : f c = d) (hcz : c = 0) (hdz : d = 0)
local notation "C" => conicCoefficientMap f W.a₁ c V.a₁ d ha hc
local notation "L" => nodalLaurentCoefficientMap f

/-- A conic ring map is determined by coefficients and the two original coordinates. -/
theorem conic_ringHom_ext {A B : Type*} [CommRing A] [CommRing B] (a e : A)
    (g h : ConicCoordinate a e →+* B)
    (hs : ∀ s, g (algebraMap A _ s) = h (algebraMap A _ s))
    (ht : g (conicT a e) = h (conicT a e))
    (hv : g (conicV a e) = h (conicV a e)) : g = h := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · exact hs
    · exact ht
  · exact hv

/-- The first full conic puncture retains its actual Laurent coefficient specialization. -/
theorem conicPuncturedFirst_coefficient :
    (conicPuncturedFirst V d hdz).toRingHom.comp C =
      (L).comp (conicPuncturedFirst W c hcz).toRingHom := by
  apply conic_ringHom_ext
  · intro s
    change conicPuncturedFirst V d hdz (C (algebraMap S _ s)) =
      L (conicPuncturedFirst W c hcz (algebraMap S _ s))
    rw [conicCoefficientMap_scalar, AlgHom.commutes, AlgHom.commutes,
      nodalLaurentCoefficientMap_scalar]
  · change conicPuncturedFirst V d hdz (C (conicT W.a₁ c)) =
      L (conicPuncturedFirst W c hcz (conicT W.a₁ c))
    rw [conicCoefficientMap_t]
    simp only [conicPuncturedFirst, conicEvaluation_t, map_mul,
      nodalLaurentCoefficientMap_character]
    rw [show LaurentPolynomial.C W.a₁ = algebraMap S S[T;T⁻¹] W.a₁ from rfl,
      nodalLaurentCoefficientMap_scalar, ha]
    rfl
  · change conicPuncturedFirst V d hdz (C (conicV W.a₁ c)) =
      L (conicPuncturedFirst W c hcz (conicV W.a₁ c))
    rw [conicCoefficientMap_v]
    simp only [conicPuncturedFirst, conicEvaluation_v, map_zero]

/-- The opposite full puncture preserves both original negative signs under specialization. -/
theorem conicPuncturedSecond_coefficient :
    (conicPuncturedSecond V d hdz).toRingHom.comp C =
      (L).comp (conicPuncturedSecond W c hcz).toRingHom := by
  apply conic_ringHom_ext
  · intro s
    change conicPuncturedSecond V d hdz (C (algebraMap S _ s)) =
      L (conicPuncturedSecond W c hcz (algebraMap S _ s))
    rw [conicCoefficientMap_scalar, AlgHom.commutes, AlgHom.commutes,
      nodalLaurentCoefficientMap_scalar]
  · change conicPuncturedSecond V d hdz (C (conicT W.a₁ c)) =
      L (conicPuncturedSecond W c hcz (conicT W.a₁ c))
    rw [conicCoefficientMap_t]
    simp only [conicPuncturedSecond, conicEvaluation_t, map_mul, map_neg,
      nodalLaurentCoefficientMap_character]
    rw [show LaurentPolynomial.C W.a₁ = algebraMap S S[T;T⁻¹] W.a₁ from rfl,
      nodalLaurentCoefficientMap_scalar, ha]
    rfl
  · change conicPuncturedSecond V d hdz (C (conicV W.a₁ c)) =
      L (conicPuncturedSecond W c hcz (conicV W.a₁ c))
    rw [conicCoefficientMap_v]
    simp only [conicPuncturedSecond, conicEvaluation_v, map_neg]
    rw [show LaurentPolynomial.C W.a₁ = algebraMap S S[T;T⁻¹] W.a₁ from rfl,
      nodalLaurentCoefficientMap_scalar, ha]
    rfl

/-- The entire first conic parameter commutes with the actual coefficient morphisms. -/
@[reassoc] theorem conicPuncturedFirst_spec_coefficient :
    Spec.map (CommRingCat.ofHom (conicPuncturedFirst V d hdz).toRingHom) ≫
        Spec.map (CommRingCat.ofHom C) =
      Spec.map (CommRingCat.ofHom L) ≫
        Spec.map (CommRingCat.ofHom (conicPuncturedFirst W c hcz).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact conicPuncturedFirst_coefficient f W V c d ha hc hcz hdz

/-- The entire signed second conic parameter commutes with the actual coefficient morphisms. -/
@[reassoc] theorem conicPuncturedSecond_spec_coefficient :
    Spec.map (CommRingCat.ofHom (conicPuncturedSecond V d hdz).toRingHom) ≫
        Spec.map (CommRingCat.ofHom C) =
      Spec.map (CommRingCat.ofHom L) ≫
        Spec.map (CommRingCat.ofHom (conicPuncturedSecond W c hcz).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact conicPuncturedSecond_coefficient f W V c d ha hc hcz hdz

end FLT.Mazur.WeierstrassModificationX
