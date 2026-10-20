/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentLowerResidue

/-!
# The constructed shallow branch forces both residue ordinates to vanish

No input branch-coordinate vanishing is assumed. The first input equation
and branch inverse give the first ordinate; the original chord relation
then gives the second, over any specialization killing the output scale.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
variable {R K : Type*} [CommRing R] [CommRing K] (f : R →+* K)
  (W : WeierstrassCurve R) (s t w b3 b4 b6 a2 b4' b6' u₁ u₂ v₁ v₂ : R)
  (hc : IsUnit (v₁ + W.a₁ * u₁ + b3))
  (hd : IsUnit (v₁ + v₂ + W.a₁ * u₂ + b3))
  (hs : s = t * w) (h2 : W.a₂ = t * a2)
  (h4 : b4 = t * b4') (h6 : b6 = t * b6')
  (h₁ : v₁ ^ 2 + (W.a₁ * u₁ + b3) * v₁ =
    s * u₁ ^ 3 + W.a₂ * u₁ ^ 2 + b4 * u₁ + b6)
  (h₂ : v₂ ^ 2 + (W.a₁ * u₂ + b3) * v₂ =
    s * u₂ ^ 3 + W.a₂ * u₂ ^ 2 + b4 * u₂ + b6)

include hc hd hs h2 h4 h6 h₁ h₂ in
/-- The constructed smaller-scale slope forces both branch ordinates to have zero residue. -/
theorem tangentLower_specialized_ordinates (ht : f t = 0) : f v₁ = 0 ∧ f v₂ = 0 := by
  have hv := congrArg f
    (tangentLowerOrdinate_mul W s t w b3 b4 b6 a2 b4' b6' u₁ v₁ hc hs h2 h4 h6 h₁)
  simp only [map_mul, ht, zero_mul] at hv
  have hl := divided_tangent_relation W s b3 b4 b6 h₁ h₂ hd
    (tangentLowerSlope_chord W s t w b3 b4 b6 a2 b4' b6' u₁ u₂ v₁ v₂
      hc hd hs h2 h4 h6 h₁)
  have hf := congrArg f hl
  simp only [map_mul, map_sub, ht, zero_mul, hv.symm, zero_sub, zero_eq_neg] at hf
  exact ⟨hv.symm, hf⟩

include hc hd hs h2 h4 h6 h₁ h₂ in
/-- Terminal smoothness follows from coefficients and actual equations alone. -/
theorem tangentLower_specialized_smooth (e3 : R)
    (ht : f t = 0) (hw : f w = 0) (h3 : f b3 = 0)
    (ha2 : f a2 = 0) (hb4 : f b4' = 0) (he3 : f e3 = 0) (hb6 : IsUnit (f b6')) :
    let l := tangentLowerSlope W w b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd
    IsUnit (f (2 * tangentLowerY W s t w b3 a2 u₁ u₂ v₁ l +
      W.a₁ * tangentLowerX W t w a2 u₁ u₂ l + e3)) := by
  have hv := tangentLower_specialized_ordinates f W s t w b3 b4 b6 a2 b4' b6'
    u₁ u₂ v₁ v₂ hc hd hs h2 h4 h6 h₁ h₂ ht
  exact tangentLower_specialized_vertical_isUnit f W s t w b3 a2 b4' b6' e3
    u₁ u₂ v₁ v₂ hc hd (by rw [hs, map_mul, ht, zero_mul]) ht hw h3 ha2 hb4 he3
    hv.1 hv.2 hb6

end FLT.Mazur.WeierstrassDilatation
