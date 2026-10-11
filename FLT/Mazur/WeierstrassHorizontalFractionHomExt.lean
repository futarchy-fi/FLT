/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesCoordinates

/-!
# Extensionality on the original horizontal fraction algebra

The proved equation equivalence transports the two-generator extensionality
criterion to the original Rees chart, without inverting its denominator.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R C : Type*} [CommRing R] [IsDomain R] [CommRing C] [Algebra R C]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
open WeierstrassModificationReesCoordinates
local notation "H" => horizontalReesChart W s
local notation "E" => horizontalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs

include h3 h4 h6 hs

/-- The original scale and slope determine an algebra map from the horizontal fraction chart. -/
theorem horizontalFraction_algHom_ext (f g : H →ₐ[R] C)
    (ht : f (horizontalScale W s) = g (horizontalScale W s))
    (hv : f (horizontalVertical W s) = g (horizontalVertical W s)) : f = g := by
  suffices h : f.comp (E).toAlgHom = g.comp (E).toAlgHom by
    apply AlgHom.ext
    intro q
    obtain ⟨t, rfl⟩ := (E).surjective q
    exact AlgHom.congr_fun h t
  apply hom_ext
  · simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      horizontalEquiv_t] using ht
  · simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      horizontalEquiv_v] using hv

/-- Coefficient compatibility and the two ratios determine the entire fraction ring map. -/
theorem horizontalFraction_ringHom_ext (f g : H →+* C)
    (hf : ∀ r, f (algebraMap R H r) = algebraMap R C r)
    (hg : ∀ r, g (algebraMap R H r) = algebraMap R C r)
    (ht : f (horizontalScale W s) = g (horizontalScale W s))
    (hv : f (horizontalVertical W s) = g (horizontalVertical W s)) : f = g := by
  let fa : H →ₐ[R] C := { f with commutes' := hf }
  let ga : H →ₐ[R] C := { g with commutes' := hg }
  exact congrArg AlgHom.toRingHom
    (horizontalFraction_algHom_ext W s b3 b4 b6 h3 h4 h6 hs fa ga ht hv)

end FLT.Mazur.WeierstrassModificationX
