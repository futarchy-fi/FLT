/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXModificationMap

/-!
# Uniqueness and residue vanishing on the incidence open

Invertible incidence determines the retained horizontal coordinate from the
original incidence relation. Consequently the two original modification
functions determine the full successive-chart map on this open.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "A" => Coordinate W s π b3 b4 b6
local notation "t" => coord W s π b3 b4 b6 0
local notation "v" => coord W s π b3 b4 b6 1
local notation "u" => coord W s π b3 b4 b6 2

/-- Invertible incidence and the original slope determine the entire successive-chart map. -/
theorem hom_ext_of_incidence_unit (f g : A →ₐ[R] S) (hu : IsUnit (f t))
    (ht : f t = g t) (hv : f v = g v) : f = g := by
  apply hom_ext
  intro i
  fin_cases i
  · exact ht
  · exact hv
  · change f u = g u
    apply hu.mul_left_cancel
    have hf := congrArg f (incidence W s π b3 b4 b6)
    have hg := congrArg g (incidence W s π b3 b4 b6)
    simp only [map_mul, AlgHom.commutes] at hf hg
    rw [ht] at hf ⊢
    exact hf.trans hg.symm

/-- Equality on original modification functions proves equality of incidence-open transports. -/
theorem hom_ext_of_modification (f g : A →ₐ[R] S) (hu : IsUnit (f t))
    (h : f.comp (modificationMap W s π b3 b4 b6) =
      g.comp (modificationMap W s π b3 b4 b6)) : f = g := by
  apply hom_ext_of_incidence_unit W s π b3 b4 b6 f g hu
  · simpa only [AlgHom.comp_apply, modificationMap_t] using
      AlgHom.congr_fun h (WeierstrassModificationX.t W (s * π) b3 b4 b6)
  · simpa only [AlgHom.comp_apply, modificationMap_v] using
      AlgHom.congr_fun h (WeierstrassModificationX.v W (s * π) b3 b4 b6)

/-- Invertible incidence forces the horizontal coordinate to vanish when pi vanishes. -/
theorem horizontal_zero_of_incidence_unit (f : A →ₐ[R] S) (hu : IsUnit (f t))
    (hπ : algebraMap R S π = 0) : f u = 0 := by
  apply hu.mul_left_cancel
  have h := congrArg f (incidence W s π b3 b4 b6)
  simpa only [map_mul, AlgHom.commutes, hπ, mul_zero] using h

end FLT.Mazur.WeierstrassSuccessiveX
