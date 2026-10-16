/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialMobiusNormalization
public import FLT.Mazur.WeierstrassModificationXArithmeticRestrictionMaps

/-!
# Full fractional initial charts at every arithmetic quotient order

Each quotient constructs its own normalized smoothing. The original full
initial-node quotient map commutes with the fractional polygon charts,
without discarding nilpotents or imposing a starting thickness of one.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (s : R)
  (U : WeierstrassCurve S) (ha' : IsUnit U.a₁) (s' : S)
  (hW : W.map f = U) (hs : f s = s')

include hW hs in
/-- Independently named target coefficients preserve the constructed normalized scale. -/
theorem initialTangentSmoothing_mapTo :
    f (initialTangentSmoothing W ha s) = initialTangentSmoothing U ha' s' := by
  subst U s'
  exact initialTangentSmoothing_map W ha s f

/-- The full original coefficient square also permits independently constructed target curves. -/
@[reassoc] theorem normalizedInitialMobiusChart_coefficientsTo :
    Spec.map (CommRingCat.ofHom (nodeOpenCoefficientRingMapTo f W s U s' hW hs)) ≫
      normalizedInitialMobiusChart W ha s = normalizedInitialMobiusChart U ha' s' ≫
        Spec.map (CommRingCat.ofHom (PolygonSmoothing.ringMap f
          (initialTangentSmoothing W ha s) (initialTangentSmoothing U ha' s')
          (initialTangentSmoothing_mapTo f W ha s U ha' s' hW hs))) := by
  subst U s'
  exact normalizedInitialMobiusChart_coefficients W ha s f

variable (π : R) (m : ℕ)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "q₀" => algebraMap R Q₀
local notation "q₁" => algebraMap R Q₁

/-- The exact normalized smoothing of the original arithmetic initial node. -/
def arithmeticInitialMobiusSmoothing : Q₀ :=
  initialTangentSmoothing (W.map q₀) (ha.map q₀) (q₀ s)

/-- The full original arithmetic node maps to its fractionally normalized polygon chart. -/
def arithmeticInitialMobiusChart : Spec (.of (PolynomialNodeOpen (W.map q₀) (q₀ s))) ⟶
    PolygonSmoothing.chart Q₀ (arithmeticInitialMobiusSmoothing W ha s π m) :=
  normalizedInitialMobiusChart (W.map q₀) (ha.map q₀) (q₀ s)

instance arithmeticInitialMobiusChart_isOpenImmersion :
    IsOpenImmersion (arithmeticInitialMobiusChart W ha s π m) :=
  normalizedInitialMobiusChart_isOpenImmersion ..

/-- The full normalized smoothing follows the actual consecutive arithmetic quotient map. -/
theorem arithmeticInitialMobiusSmoothing_restriction :
    restriction R π m (arithmeticInitialMobiusSmoothing W ha s π (m + 1)) =
      arithmeticInitialMobiusSmoothing W ha s π m :=
  initialTangentSmoothing_mapTo (restriction R π m).toRingHom (W.map q₁) (ha.map q₁)
    (q₁ s) (W.map q₀) (ha.map q₀) (q₀ s) (arithmeticInitialCurve_restriction R π m W)
    ((restriction R π m).commutes s)

/-- The actual entire initial-node quotient square commutes at every arithmetic order. -/
@[reassoc] theorem arithmeticInitialMobiusChart_restriction :
    arithmeticFullInitialNodeQuotient R π m W s ≫
      arithmeticInitialMobiusChart W ha s π (m + 1) =
        arithmeticInitialMobiusChart W ha s π m ≫
          Spec.map (CommRingCat.ofHom (PolygonSmoothing.ringMap (restriction R π m).toRingHom
            (arithmeticInitialMobiusSmoothing W ha s π (m + 1))
            (arithmeticInitialMobiusSmoothing W ha s π m)
            (arithmeticInitialMobiusSmoothing_restriction W ha s π m))) :=
  normalizedInitialMobiusChart_coefficientsTo (restriction R π m).toRingHom
    (W.map q₁) (ha.map q₁) (q₁ s) (W.map q₀) (ha.map q₀) (q₀ s)
    (arithmeticInitialCurve_restriction R π m W) ((restriction R π m).commutes s)

end FLT.Mazur.WeierstrassModificationX
