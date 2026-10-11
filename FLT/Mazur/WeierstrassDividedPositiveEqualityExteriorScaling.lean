/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityExteriorAction
public import FLT.Mazur.PolygonSplitIdentityGroup
import all FLT.Mazur.WeierstrassDividedPositiveEqualitySmoothGroup

/-!
# Exterior scaling and fixed boundary sections for the integral action

The actual coefficient action scales the complete exterior projective line in
its cyclic coordinate, and fixes both original boundary sections scheme-theoretically.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing MonoidalCategory MonObj
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
open WeierstrassIntegralChart CartesianMonoidalCategory
local notation "K" => ResidueField R
local notation "V" => W.map (algebraMap R K)
local notation "hd" => lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.succ_pos _)) hk
local notation "G" => PolygonSplitGroup.model K (2 * s + 4)
local notation "M" => positiveEqualityCycleSmoothMap hπ data D s hs hstart hk hp


local notation "U" => MultiplicativeGroupScheme.gm K
local notation "c" => PolygonSplitGroup.component K (2 * s + 4) 0
local notation "v" => positiveEqualityCyclicSmoothGroupIso D s hk
local notation "A" => positiveEqualityCycleAction hπ data D s hs hstart hk hp
local notation "B" => finiteGlobalCoefficientOverAction hπ data (s + 1) hs K
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "t" => PolygonPinching.torusToComponent K


/-- The actual specialized integral action scales the full exterior projective coordinate. -/
theorem positiveEqualityCoefficientAction_exterior_scaling :
    ((v).hom.hom.hom.hom ⊗ₘ Z 0) ≫ B =
      ProjectiveLineUniversalAction.act K ≫ Z 0 := by
  rw [positiveEqualityCycleAction_exterior, positiveEqualityCycleAction_component,
    PolygonPinching.rotateIndex_zero]

/-- Both boundary sections of the exterior component are fixed by the actual integral action. -/
theorem positiveEqualityCoefficientAction_exterior_endpoint (b : Bool) :
    ((v).hom.hom.hom.hom ⊗ₘ
        (ProjectiveLineActionEndpoints.endpointSection K b ≫ Z 0)) ≫ B =
      snd U (PolygonPinching.point K) ≫
        ProjectiveLineActionEndpoints.endpointSection K b ≫ Z 0 := by
  rw [← whiskerLeft_comp_tensorHom_assoc, positiveEqualityCoefficientAction_exterior_scaling]
  rw [reassoc_of% (ProjectiveLineActionEndpoints.section_act K b)]

variable (T : Over (Spec (CommRingCat.of (ResidueField R))))

/-- Every relative point of the complete exterior component scales by the actual action. -/
theorem positiveEqualityCoefficientAction_exterior_point
    (a : T ⟶ U) (b : T ⟶ PolygonPinching.component K) :
    (a ≫ (v).hom.hom.hom.hom) • (b ≫ Z 0) =
      lift a b ≫ ProjectiveLineUniversalAction.act K ≫ Z 0 := by
  rw [← finiteGlobalCoefficientOverAction_points, ← lift_map_assoc,
    positiveEqualityCoefficientAction_exterior_scaling]

/-- The fixed boundary formula holds for arbitrary original smooth parameters. -/
theorem positiveEqualityCoefficientAction_exterior_endpoint_point
    (a : T ⟶ (integralSmoothGroup V).X) (b : T ⟶ PolygonPinching.point K) (e : Bool) :
    a • (b ≫ ProjectiveLineActionEndpoints.endpointSection K e ≫ Z 0) =
      b ≫ ProjectiveLineActionEndpoints.endpointSection K e ≫ Z 0 := by
  have h := congrArg (lift (a ≫ (v).inv.hom.hom.hom) b ≫ ·)
    (positiveEqualityCoefficientAction_exterior_endpoint hπ data D s hs hstart hk hp e)
  rw [← Category.assoc, lift_map, finiteGlobalCoefficientOverAction_points] at h
  have hi : (v).inv.hom.hom.hom ≫ (v).hom.hom.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom.hom) (v).inv_hom_id
  simpa only [Category.assoc, lift_snd_assoc, hi, Category.comp_id] using h

end FLT.Mazur.WeierstrassDividedDepth
