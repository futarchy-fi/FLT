/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialMobiusEquiv
public import FLT.Mazur.NodalFiberTangentMobiusCoefficientGeometry
public import FLT.Mazur.WeierstrassModificationXNodeOpenCoefficientMap

/-!
# Constructed tangent normalization for the full original arithmetic initial chart

Dividing the original smoothing by the square of its tangent unit supplies
the required normalization for every starting thickness. Its complete polygon
chart commutes with the original coefficient map on the full node neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (s : R)
local notation "a" => zeroInitialTangentUnit W ha

/-- The normalized smoothing is constructed from the original scale and its tangent unit. -/
def initialTangentSmoothing : R := (↑a⁻¹ : R) ^ 2 * s

/-- The original scale has exactly the square tangent factor required by the fractional chart. -/
theorem initialTangentSmoothing_factor : s = W.a₁ ^ 2 * initialTangentSmoothing W ha s := by
  have hi : W.a₁ * (↑a⁻¹ : R) = 1 := (a).mul_inv
  dsimp only [initialTangentSmoothing]
  rw [show W.a₁ ^ 2 * ((↑a⁻¹ : R) ^ 2 * s) = (W.a₁ * (↑a⁻¹ : R)) ^ 2 * s by ring]
  rw [hi, one_pow, one_mul]

/-- The normalized smoothing recovers zero on the original zero fiber. -/
@[simp] theorem initialTangentSmoothing_zero : initialTangentSmoothing W ha 0 = 0 := by
  rw [initialTangentSmoothing, mul_zero]

/-- The entire original arithmetic node has a constructed full fractional polygon chart. -/
def normalizedInitialMobiusChart : Spec (.of (PolynomialNodeOpen W s)) ⟶
    PolygonSmoothing.chart R (initialTangentSmoothing W ha s) :=
  initialMobiusChart W ha s (initialTangentSmoothing W ha s) (initialTangentSmoothing_factor W ha s)

instance normalizedInitialMobiusChart_isOpenImmersion :
    IsOpenImmersion (normalizedInitialMobiusChart W ha s) :=
  initialMobiusChart_isOpenImmersion ..

variable {S : Type u} [CommRing S] (f : R →+* S)

/-- The tangent unit is the original coefficient unit after arbitrary coefficient extension. -/
theorem initialTangentUnit_map :
    Units.map f.toMonoidHom a = zeroInitialTangentUnit (W.map f) (ha.map f) :=
  Units.ext rfl

/-- The constructed normalized smoothing follows the actual original coefficient map. -/
theorem initialTangentSmoothing_map :
    f (initialTangentSmoothing W ha s) = initialTangentSmoothing (W.map f) (ha.map f) (f s) := by
  have hi := congrArg (fun u : Sˣ ↦ (↑u⁻¹ : S)) (initialTangentUnit_map W ha f)
  change f (↑a⁻¹ : R) = (↑(zeroInitialTangentUnit (W.map f) (ha.map f))⁻¹ : S) at hi
  simp only [initialTangentSmoothing, map_mul, map_pow, hi]

/-- The complete normalized initial chart commutes with the original full coefficient map. -/
@[reassoc] theorem normalizedInitialMobiusChart_coefficients :
    Spec.map (CommRingCat.ofHom (nodeOpenCoefficientRingMap f W s)) ≫
      normalizedInitialMobiusChart W ha s =
        normalizedInitialMobiusChart (W.map f) (ha.map f) (f s) ≫
          Spec.map (CommRingCat.ofHom (PolygonSmoothing.ringMap f
            (initialTangentSmoothing W ha s)
            (initialTangentSmoothing (W.map f) (ha.map f) (f s))
            (initialTangentSmoothing_map W ha s f))) := by
  have h := NodalFiber.tangentMobiusChart_coefficients f s (initialTangentSmoothing W ha s)
    a (initialTangentSmoothing_factor W ha s) (f s)
    (initialTangentSmoothing (W.map f) (ha.map f) (f s)) rfl
    (initialTangentSmoothing_map W ha s f)
  have he : NodalFiber.tangentMobiusChart (f s)
      (initialTangentSmoothing (W.map f) (ha.map f) (f s)) (Units.map f.toMonoidHom a)
      (NodalFiber.tangentMobius_smoothing_map f s (initialTangentSmoothing W ha s)
        a (initialTangentSmoothing_factor W ha s) (f s)
        (initialTangentSmoothing (W.map f) (ha.map f) (f s)) rfl
        (initialTangentSmoothing_map W ha s f)) =
      normalizedInitialMobiusChart (W.map f) (ha.map f) (f s) := by
    unfold normalizedInitialMobiusChart initialMobiusChart
    congr 1
    exact initialTangentUnit_map W ha f
  rw [he] at h
  exact h

end FLT.Mazur.WeierstrassModificationX
