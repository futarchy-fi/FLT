/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearConicParameters
public import FLT.Mazur.WeierstrassConicZeroAffineParameter
public import FLT.Mazur.WeierstrassSuccessiveXMiddleIntersection
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Actual retained node attachments in the coefficient gluing

The original conic markings and line origins remain the scheme-theoretic
intersections after embedding the complete middle chart in the actual model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (t : ℕ) (ht : t ≤ n) (i : Fin t)
local notation "d" => data (Fin.mk (i.val + 1) (by omega))
local notation "q" => algebraMap R S
local notation "U" => rootShearCurve (W.map q) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => q (Data.b6 d)
variable (hs : algebraMap R S (π ^ (start + i.val)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨i.val + 1, by omega⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨i.val + 1, by omega⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "h2" => coefficientShear_a₂_zero W S r hr

local notation "F" => coefficientShearRetainedFiber hπ data S r t ht i hs hp h3 h4
local notation "C" => coefficientShearRetainedConic hπ data S r t ht i hs hp h3 h4 hr
local notation "L" => coefficientShearRetainedLine hπ data S r t ht i hs hp h3 h4 hr
variable (ha : IsUnit (rootShearCurve (W.map (algebraMap R S)) r).a₁)

/-- The first actual conic-line intersection is the base with its original markings. -/
theorem coefficientShearRetainedFirstAttachment_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint a c ha).toRingHom))
      (ProjectiveLine.chartZero S) C (L 0 (middle_first_root U)) := by
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ F
    (middleFirstAttachment_isPullback U c h2 ha).cone
    (middleFirstAttachment_isPullback U c h2 ha).isLimit)

/-- The opposite actual intersection retains its negative tangent slope. -/
theorem coefficientShearRetainedSecondAttachment_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint a c ha).toRingHom))
      (ProjectiveLine.chartZero S) C (L (-a) (middle_second_root U)) := by
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ F
    (middleSecondAttachment_isPullback U c h2 ha).cone
    (middleSecondAttachment_isPullback U c h2 ha).isLimit)

/-- The first conic marking is exactly the actual retained first-line origin. -/
theorem coefficientShearRetainedFirstAttachment :
    Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint a c ha).toRingHom) ≫ C =
      ProjectiveLine.chartZero S ≫ L 0 (middle_first_root U) :=
  (coefficientShearRetainedFirstAttachment_isPullback
    hπ data S r t ht i hs hp h3 h4 hr ha).w

/-- The opposite conic marking is exactly the actual retained second-line origin. -/
theorem coefficientShearRetainedSecondAttachment :
    Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint a c ha).toRingHom) ≫ C =
      ProjectiveLine.chartZero S ≫ L (-a) (middle_second_root U) :=
  (coefficientShearRetainedSecondAttachment_isPullback
    hπ data S r t ht i hs hp h3 h4 hr ha).w

end FLT.Mazur.WeierstrassDividedDepth
