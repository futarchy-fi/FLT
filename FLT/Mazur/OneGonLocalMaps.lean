/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.OneGonLocalizedPinching

/-!
# Local morphisms descending through the pinching

The localized equalizer description constructs ring maps and hence scheme
maps, together with their normalization equations and uniqueness.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.PolygonNodePresentation
open FLT.Mazur.OneGonLocalizedPinching

namespace FLT.Mazur.OneGonLocalMaps

universe u
variable {K A : Type u} [Field K] [CommRing A]
variable (s : B (R := K)) (hs : bEval s ≠ 0)

/-- The restriction map identifies the localized chart with its actual image. -/
def imageEquiv : chart s ≃+* (restriction s).range :=
  RingEquiv.ofBijective (restriction s).rangeRestrict
    ⟨fun _a _b h ↦ restriction_injective s (congrArg Subtype.val h),
      (restriction s).rangeRestrict_surjective⟩

/-- Descend an affine-target ring map whose endpoint values agree. -/
def descend (φ : A →+* line s)
    (hφ : (atZero s hs).comp φ = (atOne s hs).comp φ) : A →+* chart s :=
  (imageEquiv s).symm.toRingHom.comp
    (φ.codRestrict (restriction s).range fun a ↦ by
      rw [range_restriction s hs]
      exact RingHom.congr_fun hφ a)

/-- Pulling the descended functions back recovers the original functions. -/
theorem restriction_descend (φ : A →+* line s)
    (hφ : (atZero s hs).comp φ = (atOne s hs).comp φ) :
    (restriction s).comp (descend s hs φ hφ) = φ := by
  apply RingHom.ext
  intro a
  exact congrArg Subtype.val ((imageEquiv s).apply_symm_apply
    (φ.codRestrict (restriction s).range (fun a ↦ by
      rw [range_restriction s hs]
      exact RingHom.congr_fun hφ a) a))

/-- The descended ring map is unique. -/
theorem descend_unique (φ : A →+* line s)
    (hφ : (atZero s hs).comp φ = (atOne s hs).comp φ)
    (ψ : A →+* chart s) (hψ : (restriction s).comp ψ = φ) :
    ψ = descend s hs φ hφ := by
  apply RingHom.ext
  intro a
  apply restriction_injective s
  exact (RingHom.congr_fun hψ a).trans
    (RingHom.congr_fun (restriction_descend s hs φ hφ) a).symm

/-- The actual scheme morphism on the principal neighborhood of the node. -/
def localMap (φ : A →+* line s)
    (hφ : (atZero s hs).comp φ = (atOne s hs).comp φ) :
    Spec (.of (chart s)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (descend s hs φ hφ))

/-- The local map recovers the prescribed map on the localized normalization. -/
theorem normalization_localMap (φ : A →+* line s)
    (hφ : (atZero s hs).comp φ = (atOne s hs).comp φ) :
    Spec.map (CommRingCat.ofHom (restriction s)) ≫ localMap s hs φ hφ =
      Spec.map (CommRingCat.ofHom φ) := by
  rw [localMap, ← Spec.map_comp]
  exact congrArg (fun f : A →+* line s ↦ Spec.map (CommRingCat.ofHom f))
    (restriction_descend s hs φ hφ)

end FLT.Mazur.OneGonLocalMaps
