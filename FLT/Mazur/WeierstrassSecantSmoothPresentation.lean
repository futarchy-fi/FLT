/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSecantPairRefinement

/-!
# The secant refinement retains the actual smooth action and normalized input

Both the smooth point and the original input are pulled back to the concrete
secant open. The ordinary output is their genuine sum. A common normalized
Y-chart gives the cross-coordinate identities after every residue restriction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (a c : Coordinate W 2 →ₐ[R] S)
local notation "T" => SecantPairRing W a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "ι" => Spec.map (CommRingCat.ofHom (algebraMap S T))
variable (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme)
  (ha : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ integralCurveChart W 2 =
    p ≫ (integralSmoothOpen W).ι)
  (hp : p ≫ integralSmoothStructure W =
    (Spec.map (CommRingCat.ofHom c.toRingHom) ≫ integralCurveChart W 2) ≫
      integralCurveStructure W)

include hp in
/-- Pulling the actual pair to the secant open preserves coefficient compatibility. -/
theorem secantPairSmooth_structure :
    (ι ≫ p) ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom ((j).comp c).toRingHom) ≫
        integralCurveChart W 2) ≫ integralCurveStructure W := by
  rw [Category.assoc, hp, ← Category.assoc, ← Category.assoc, ← Spec.map_comp]
  rfl

include ha hp in
/-- The concrete secant output is the actual pulled-back smooth action. -/
theorem secantPairSmooth_addition :
    Spec.map (CommRingCat.ofHom
      ((secantPairPresentation W a c).comp (ordinaryChartAddition W false)).toRingHom) ≫
        integralCurveChart W 2 =
      leftSmoothPointAddition W (ι ≫ p)
        (Spec.map (CommRingCat.ofHom ((j).comp c).toRingHom) ≫ integralCurveChart W 2)
        (secantPairSmooth_structure W a c p hp) := by
  apply ordinaryPairPresentation_addition W ((j).comp a) ((j).comp c) false
    (secantPair_denominator W a c) (ι ≫ p)
  rw [Category.assoc, ← ha, ← Category.assoc, ← Spec.map_comp]
  rfl

variable (v : Coordinate W 1 →ₐ[R] S)
  (hv : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ integralCurveChart W 2 =
    Spec.map (CommRingCat.ofHom v.toRingHom) ≫ integralCurveChart W 1)
  {C : Type*} [CommRing C] (e : SecantPairRing W a c →+* C)

include hv in
/-- Actual affine/Y overlap supplies every cross-coordinate identity needed by residue action. -/
theorem secantPairSmooth_cross (i : Fin 3) :
    e (secantPairPresentation W a c (ordinaryInputLeft W false (coord W 2 i))) =
      e (secantPairPresentation W a c (ordinaryInputLeft W false (coord W 2 1))) *
        e (algebraMap S T (v (coord W 1 i))) := by
  have cross := (chart_algHom_global_eq_iff W 2 1 a v).mp hv i
  have left (t : Coordinate W 2) :
      secantPairPresentation W a c (ordinaryInputLeft W false t) = algebraMap S T (a t) :=
    DFunLike.congr_fun (secantPairPresentation_left W a c) t
  rw [left, left, cross, map_mul, map_mul]

end FLT.Mazur.WeierstrassIntegralChart
