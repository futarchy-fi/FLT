/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearScaleOne
public import FLT.Mazur.WeierstrassModificationXFiberExteriorSlope
public import FLT.Mazur.PrincipalOpenTransport

/-!
# The first retained horizontal boundary at scale one

The whole original tensor horizontal open is the punctured slope line.
Its incidence vanishes, while its original slope retains the tangent-root shift.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "a" => WeierstrassCurve.a₁ (rootShearCurve (W.map (algebraMap R S)) r)
local notation "c" => algebraMap R S b6
local notation "T" => ScalarExtension W s π b3 b4 b6 S
local notation "F" => FiberCoordinate a c
local notation "P" => SlopeOpen a
local notation "u" => tensorCoord W s π b3 b4 b6 S 2
local notation "E" => tensorShearScaleOneFiberEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr

/-- The original horizontal tensor function is exactly the full conic factor. -/
theorem tensorShearScaleOneFiberEquiv_horizontal : E u = fiberConicFactor a c := by
  rw [tensorShearScaleOneFiberEquiv_coord]
  change fiberV a c ^ 2 + algebraMap S F a * fiberV a c -
    algebraMap S F c * fiberT a c ^ 2 = _
  unfold fiberConicFactor
  ring

/-- The entire original horizontal localization has the canonical slope coordinates. -/
def tensorShearScaleOneHorizontalEquiv : Localization.Away u ≃ₐ[S] P :=
  (PrincipalOpenTransport.equiv E u (fiberConicFactor a c)
    (tensorShearScaleOneFiberEquiv_horizontal W s π b3 b4 b6 S r hs hp h3 h4 hr)).trans
      (fiberExteriorSlopeEquiv a c)

/-- Every original tensor function restricts through the original incidence line. -/
theorem tensorShearScaleOneHorizontalEquiv_base (z : T) :
    tensorShearScaleOneHorizontalEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr
      (algebraMap T _ z) = algebraMap (Polynomial S) P (fiberIncidenceMap a c (E z)) := by
  rw [tensorShearScaleOneHorizontalEquiv, AlgEquiv.trans_apply,
    PrincipalOpenTransport.equiv_base, fiberExteriorSlopeEquiv_base]

/-- The first retained boundary keeps all three original tensor coordinate formulas. -/
theorem tensorShearScaleOneHorizontalEquiv_coord (i : Fin 3) :
    tensorShearScaleOneHorizontalEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr
      (algebraMap T _ (tensorCoord W s π b3 b4 b6 S i)) =
        ![0, slopeZ a + algebraMap S P r,
          slopeZ a * (slopeZ a + algebraMap S P a)] i := by
  rw [tensorShearScaleOneHorizontalEquiv_base, tensorShearScaleOneFiberEquiv_coord]
  fin_cases i
  · change algebraMap (Polynomial S) P (fiberIncidenceMap a c (fiberT a c)) = 0
    rw [fiberIncidenceMap_t, map_zero]
  · change algebraMap (Polynomial S) P
      (fiberIncidenceMap a c (fiberV a c + algebraMap S F r)) = _
    rw [map_add, fiberIncidenceMap_v, AlgHom.commutes, map_add]
    rfl
  · change algebraMap (Polynomial S) P
      (fiberIncidenceMap a c (fiberV a c ^ 2 + algebraMap S F a * fiberV a c -
        algebraMap S F c * fiberT a c ^ 2)) = _
    simp only [map_sub, map_add, map_mul, map_pow, AlgHom.commutes, fiberIncidenceMap_v,
      fiberIncidenceMap_t, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero,
      ← IsScalarTower.algebraMap_apply S (Polynomial S) P]
    change slopeZ a ^ 2 + algebraMap S P a * slopeZ a =
      slopeZ a * (slopeZ a + algebraMap S P a)
    ring

end FLT.Mazur.WeierstrassSuccessiveX
