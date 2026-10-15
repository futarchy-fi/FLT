/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationArithmeticTensorRestriction

/-!
# Ring maps from the full cubic tensor algebra

Constants in the extended coefficient ring and the two original pure tensor
coordinates determine a ring map without expanding tensor operations.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- Original tensor coordinates and extended constants determine every ring map. -/
theorem tensor_coefficient_ringHom_ext
    (g h : ScalarExtension W s b3 b4 b6 S →+* A)
    (hc : ∀ a, g (algebraMap S _ a) = h (algebraMap S _ a))
    (hx : g ((1 : S) ⊗ₜ[R] x W s b3 b4 b6) = h ((1 : S) ⊗ₜ[R] x W s b3 b4 b6))
    (hy : g ((1 : S) ⊗ₜ[R] y W s b3 b4 b6) = h ((1 : S) ⊗ₜ[R] y W s b3 b4 b6)) :
    g = h := by
  have he : g.comp (baseChangeBackward W s b3 b4 b6 S).toRingHom =
      h.comp (baseChangeBackward W s b3 b4 b6 S).toRingHom := by
    apply coefficient_ringHom_ext
    · intro a
      simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        AlgHom.commutes] using hc a
    · simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        baseChangeBackward_x] using hx
    · simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        baseChangeBackward_y] using hy
  apply RingHom.ext
  intro z
  have hz := DFunLike.congr_fun he (baseChangeForward W s b3 b4 b6 S z)
  have hi := DFunLike.congr_fun (baseChangeBackward_forward W s b3 b4 b6 S) z
  change baseChangeBackward W s b3 b4 b6 S (baseChangeForward W s b3 b4 b6 S z) = z at hi
  simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hi] using hz

end FLT.Mazur.WeierstrassDilatation
