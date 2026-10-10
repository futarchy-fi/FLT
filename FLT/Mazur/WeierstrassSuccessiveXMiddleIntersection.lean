/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SurjectiveKernelPushout
public import FLT.Mazur.WeierstrassSuccessiveXMiddleIncidence
public import FLT.Mazur.WeierstrassSuccessiveXMiddleComponents
public import FLT.Mazur.WeierstrassModificationXConicIncidenceOrientation
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual ordered conic-line intersection squares

The existing summed-kernel calculation gives a cartesian square of schemes,
with the original conic marking and line origin as its two projections.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (c : R) (h2 : W.a₂ = 0)
  (r : R) (hr : r * (r + W.a₁) = 0)
local notation "f₀" => middleConicMap W c h2
local notation "g₀" => middleLineMap W c h2 r hr
/-- The conic marking with the specified original tangent root. -/
def middleConicAttachmentPoint : ConicCoordinate W.a₁ c →ₐ[R] R :=
  conicEvaluation W.a₁ c 0 r (by simpa using hr)

local notation "l₀" => middleConicAttachmentPoint W c r hr
local notation "z" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (aeval (0 : R))))

/-- The entire conic-line intersection is the base, with both actual evaluation maps. -/
theorem middleAttachment_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (AlgHom.toRingHom l₀))) z
      (middleConicImmersion W c h2) (middleLineImmersion W c h2 r hr) := by
  apply isPullback_SpecMap_of_isPushout
  apply SurjectiveKernelPushout.isPushout (AlgHom.toRingHom f₀) (AlgHom.toRingHom g₀)
    (AlgHom.toRingHom l₀) (AlgHom.toRingHom (aeval (0 : R)))
    (middleConicMap_surjective W c h2) (middleLineMap_surjective W c h2 r hr)
  · intro x
    exact ⟨algebraMap R (Coordinate W 0 0 0 0 c) x,
      ((l₀).comp f₀).commutes x⟩
  · exact congrArg AlgHom.toRingHom (middleAttachment_conic W c h2 r hr)
  · change RingHom.ker ((l₀).comp f₀) = RingHom.ker f₀ ⊔ RingHom.ker g₀
    rw [middleConicAttachmentPoint, middleAttachment_conic W c h2 r hr,
      middleAttachment_ker W c h2 r hr,
      middleConicMap_ker, middleLineMap_ker]

/-- The original first conic marking is precisely evaluation at the zero tangent root. -/
theorem middleFirstConicMarking (ha : IsUnit W.a₁) :
    conicFirstIncidencePoint W.a₁ c ha =
      conicEvaluation W.a₁ c 0 0 (by simp) := by
  apply conic_hom_ext
  · rw [conicFirstIncidencePoint_t, conicEvaluation_t]
  · rw [conicFirstIncidencePoint_v, conicEvaluation_v]

/-- The original opposite conic marking keeps the negative tangent root. -/
theorem middleSecondConicMarking (ha : IsUnit W.a₁) :
    conicSecondIncidencePoint W.a₁ c ha =
      conicEvaluation W.a₁ c 0 (-W.a₁) (by simp) := by
  apply conic_hom_ext
  · rw [conicSecondIncidencePoint_t, conicEvaluation_t]
  · rw [conicSecondIncidencePoint_v, conicEvaluation_v]

/-- The first full intersection square uses the established first conic marking. -/
theorem middleFirstAttachment_isPullback (ha : IsUnit W.a₁) :
    IsPullback (Spec.map (CommRingCat.ofHom
      (conicFirstIncidencePoint W.a₁ c ha).toRingHom)) z
      (middleConicImmersion W c h2)
      (middleLineImmersion W c h2 0 (middle_first_root W)) := by
  rw [middleFirstConicMarking]
  exact middleAttachment_isPullback W c h2 0 (middle_first_root W)

/-- The second full intersection square uses the established opposite conic marking. -/
theorem middleSecondAttachment_isPullback (ha : IsUnit W.a₁) :
    IsPullback (Spec.map (CommRingCat.ofHom
      (conicSecondIncidencePoint W.a₁ c ha).toRingHom)) z
      (middleConicImmersion W c h2)
      (middleLineImmersion W c h2 (-W.a₁) (middle_second_root W)) := by
  rw [middleSecondConicMarking]
  exact middleAttachment_isPullback W c h2 (-W.a₁) (middle_second_root W)

end FLT.Mazur.WeierstrassSuccessiveX
