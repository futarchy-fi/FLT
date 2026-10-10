/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginPoleBounds
public import FLT.Mazur.WeierstrassOriginIdealSheaf
public import FLT.Mazur.DivisorLineBundle

/-!
# Pole bounds as extensions of multiplication on the actual origin ideal

A regular pole numerator is equivalent to a functional on the original
powered augmentation ideal whose punctured restriction is multiplication
by the original affine function. This is the local dual-ideal comparison.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The actual augmentation ideal power in the original parameter ring. -/
def originParameterIdealPower (n : ℕ) : Ideal (OriginNeighborhood W) :=
  RingHom.ker (originEvaluation W).toRingHom ^ n

/-- Its equation is the corresponding original regular parameter power. -/
theorem originParameterIdealPower_eq (n : ℕ) :
    originParameterIdealPower W n = Ideal.span {originCoordinate W 0 ^ n} := by
  rw [originParameterIdealPower, originEvaluation_kernel, Ideal.span_singleton_pow]

/-- An explicit pole bound is exactly extension of multiplication to the actual dual ideal. -/
theorem originPole_dual_iff (a : Coordinate W 2) (n : ℕ) :
    HasOriginPoleBound W a n ↔
      ∃ φ : Module.Dual (OriginNeighborhood W) (originParameterIdealPower W n),
        ∀ b : originParameterIdealPower W n,
          algebraMap (OriginNeighborhood W) (OriginPuncture W) (φ b) =
            originPunctureAffine W a * algebraMap (OriginNeighborhood W) (OriginPuncture W) b := by
  constructor
  · rintro ⟨c, hc⟩
    let e := FCurve.CartierModule.idealEquiv (originParameterIdealPower W n)
      (originCoordinate W 0 ^ n) ((originCoordinate_x_regular W).pow n)
      (originParameterIdealPower_eq W n)
    refine ⟨(LinearMap.mulRight (OriginNeighborhood W) c).comp e.symm.toLinearMap, ?_⟩
    intro b
    obtain ⟨r, rfl⟩ := e.surjective b
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.mulRight_apply]
    change algebraMap (OriginNeighborhood W) (OriginPuncture W) (r * c) =
      originPunctureAffine W a * algebraMap (OriginNeighborhood W) (OriginPuncture W)
        (r * originCoordinate W 0 ^ n)
    rw [map_mul, hc, map_mul, map_pow, originPuncture_parameter]
    ring
  · rintro ⟨φ, hφ⟩
    let b : originParameterIdealPower W n := ⟨originCoordinate W 0 ^ n, by
      rw [originParameterIdealPower_eq]
      exact Ideal.subset_span (Set.mem_singleton _)⟩
    refine ⟨φ b, ?_⟩
    simpa only [b, map_pow, originPuncture_parameter] using hφ b

/-- The extended multiplication functional is unique on the original ideal, not just on points. -/
theorem originPole_dual_unique (a : Coordinate W 2) (n : ℕ)
    (φ ψ : Module.Dual (OriginNeighborhood W) (originParameterIdealPower W n))
    (hφ : ∀ b : originParameterIdealPower W n,
      algebraMap (OriginNeighborhood W) (OriginPuncture W) (φ b) =
        originPunctureAffine W a * algebraMap (OriginNeighborhood W) (OriginPuncture W) b)
    (hψ : ∀ b : originParameterIdealPower W n,
      algebraMap (OriginNeighborhood W) (OriginPuncture W) (ψ b) =
        originPunctureAffine W a * algebraMap (OriginNeighborhood W) (OriginPuncture W) b) :
    φ = ψ := by
  ext b
  exact originPunctureRestriction_injective W ((hφ b).trans (hψ b).symm)

end FLT.Mazur.WeierstrassIntegralChart
