/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedKernelPathCompatibility

/-!
# Explicit principal overlap comparison maps

The overlap is the iterated localization of an ambient ring at two chosen
denominators. Both chart maps and the localized quotient comparison are
constructed. A commuting equation on the ambient ring suffices to compare
the full localized paths and hence their kernels.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PrincipalLocalizedKernelPaths

universe u v w

variable {P : Type u} [CommRing P] (r s : P)

/-- The overlap, viewed from the chart where `s` is already invertible. -/
abbrev Overlap := Localization.Away (algebraMap P (Localization.Away s) r)

/-- The restriction from the other principal open to the iterated overlap. -/
def left : Localization.Away r →+* Overlap r s :=
  IsLocalization.Away.lift r
    (g := (algebraMap (Localization.Away s) (Overlap r s)).comp
      (algebraMap P (Localization.Away s)))
    (IsLocalization.Away.algebraMap_isUnit (R := Localization.Away s)
      (S := Overlap r s) (algebraMap P (Localization.Away s) r))

/-- The left restriction and the right restriction agree on the ambient ring. -/
theorem left_square :
    (left r s).comp (algebraMap P (Localization.Away r)) =
      (algebraMap (Localization.Away s) (Overlap r s)).comp
        (algebraMap P (Localization.Away s)) := by
  ext x
  exact IsLocalization.Away.lift_eq r
    (IsLocalization.Away.algebraMap_isUnit (R := Localization.Away s)
      (S := Overlap r s) (algebraMap P (Localization.Away s) r)) x

variable {A : Type v} [CommRing A] (f : Localization.Away s →+* A)

/-- The localized target of the quotient on the right principal open. -/
abbrev Target := Localization.Away (f (algebraMap P (Localization.Away s) r))

/-- The actual map between the source overlap and the localized quotient target. -/
def quotientMap : Overlap r s →+* Target r s f :=
  LocalizedKernelComparison.comparison (algebraMap P (Localization.Away s) r) f

/-- An ambient path equation extends uniquely across the other principal localization. -/
theorem quotientMap_left {B : Type w} [CommRing B]
    (g : Localization.Away r →+* B) (b : B →+* Target r s f)
    (h : (b.comp g).comp (algebraMap P (Localization.Away r)) =
      ((algebraMap A (Target r s f)).comp f).comp (algebraMap P (Localization.Away s))) :
    (quotientMap r s f).comp (left r s) = b.comp g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  rw [RingHom.comp_assoc, left_square, ← RingHom.comp_assoc]
  change ((LocalizedKernelComparison.comparison _ f).comp
    (algebraMap (Localization.Away s) (Overlap r s))).comp _ = _
  rw [LocalizedKernelComparison.comparison_square, h]

/-- The explicit overlap paths force inclusion of the full extended kernel ideals. -/
theorem map_ker_le {B : Type w} [CommRing B]
    (g : Localization.Away r →+* B) (b : B →+* Target r s f)
    (h : (b.comp g).comp (algebraMap P (Localization.Away r)) =
      ((algebraMap A (Target r s f)).comp f).comp (algebraMap P (Localization.Away s))) :
    (RingHom.ker g).map (left r s) ≤
      (RingHom.ker f).map (algebraMap (Localization.Away s) (Overlap r s)) :=
  LocalizedKernelComparison.map_ker_le_of_comparison_path _ f g (left r s) b
    (quotientMap_left r s f g b h)

/-- Killed ambient numerators are compatible after multiplying by a denominator power. -/
theorem exists_pow_mul_eq_zero {B : Type w} [CommRing B]
    (g : Localization.Away r →+* B) (b : B →+* Target r s f)
    (h : (b.comp g).comp (algebraMap P (Localization.Away r)) =
      ((algebraMap A (Target r s f)).comp f).comp (algebraMap P (Localization.Away s)))
    (x : P) (hx : g (algebraMap P (Localization.Away r) x) = 0) :
    ∃ n : ℕ, f (algebraMap P (Localization.Away s) (r ^ n * x)) = 0 :=
  LocalizedKernelComparison.exists_pow_mul_eq_zero_of_paths r x
    (algebraMap P (Localization.Away r)) (algebraMap P (Localization.Away s)) g f
    (left r s) b (left_square r s) (quotientMap_left r s f g b h) hx

end FLT.Mazur.PrincipalLocalizedKernelPaths
