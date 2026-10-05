/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardQuotient

/-!
# Normalization of Picard classes along a section

For a pointed scheme over a base, remove the pullback of the restriction at
the section. This identifies relative Picard classes with the kernel of
restriction. A kernel class has trivializable restriction; it does not include
a chosen rigidification, and no representability theorem is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.SchemePicard

variable {X S : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X)

/-- Divide by the base line bundle obtained by restriction along the section. -/
def normalize : Pic X →* Pic X where
  toFun a := a / pullback f (pullback e a)
  map_one' := by simp
  map_mul' a b := by simp only [map_mul, mul_div_mul_comm]

/-- The normalization formula for a Picard class. -/
theorem normalize_apply (a : Pic X) :
    normalize f e a = a / pullback f (pullback e a) := rfl

/-- A normalized class restricts trivially along the section. -/
@[simp]
theorem pullback_normalize (he : e ≫ f = 𝟙 S) (a : Pic X) : pullback e (normalize f e a) = 1 := by
  rw [normalize_apply, map_div, pullback_section f e he, div_self']

/-- Classes from the base normalize to the neutral class. -/
@[simp]
theorem normalize_pullback (he : e ≫ f = 𝟙 S) (a : Pic S) : normalize f e (pullback f a) = 1 := by
  rw [normalize_apply, pullback_section f e he, div_self']

/-- Normalization is unchanged by a base twist. -/
theorem normalize_base_twist (he : e ≫ f = 𝟙 S) (a : Pic X) (b : Pic S) :
    normalize f e (a * pullback f b) = normalize f e a := by
  rw [map_mul, normalize_pullback f e he, mul_one]

/-- A class whose restriction is trivial is already normalized. -/
theorem normalize_of_mem_kernel (a : Pic X) (ha : pullback e a = 1) :
    normalize f e a = a := by
  simp [normalize_apply, ha]

/-- Normalization is idempotent. -/
@[simp]
theorem normalize_idempotent (he : e ≫ f = 𝟙 S) (a : Pic X) :
    normalize f e (normalize f e a) = normalize f e a :=
  normalize_of_mem_kernel f e _ (pullback_normalize f e he a)

/-- Normalization takes values in the kernel of restriction to the section. -/
def normalizeToKernel (he : e ≫ f = 𝟙 S) : Pic X →* (pullback e).ker :=
  (normalize f e).codRestrict (pullback e).ker (pullback_normalize f e he)

/-- Normalization factors through the quotient by base line bundles. -/
def relativeNormalize (he : e ≫ f = 𝟙 S) : RelativePic f →* (pullback e).ker :=
  QuotientGroup.lift _ (normalizeToKernel f e he) (by
    rintro a ⟨b, rfl⟩
    apply Subtype.ext
    exact normalize_pullback f e he b)

/-- The factored map is normalization on representatives. -/
@[simp]
theorem relativeNormalize_class (he : e ≫ f = 𝟙 S) (a : Pic X) :
    relativeNormalize f e he (relativeClass f a) = normalizeToKernel f e he a := rfl

/-- Normalization preserves the relative class. -/
@[simp]
theorem relativeClass_normalize (a : Pic X) :
    relativeClass f (normalize f e a) = relativeClass f a := by
  rw [normalize_apply, map_div, relativeClass_pullback, div_one]

/-- Relative classes are exactly the classes trivial on the chosen section. -/
def relativeKernelEquiv (he : e ≫ f = 𝟙 S) : RelativePic f ≃* (pullback e).ker where
  toFun := relativeNormalize f e he
  invFun a := relativeClass f a.val
  left_inv a := by
    obtain ⟨a, rfl⟩ := relativeClass_surjective f a
    exact relativeClass_normalize f e a
  right_inv a := by
    apply Subtype.ext
    exact normalize_of_mem_kernel f e a.val a.property
  map_mul' := map_mul (relativeNormalize f e he)

/-- The representative of the pointed relative class is its normalized class. -/
@[simp]
theorem relativeKernelEquiv_class (he : e ≫ f = 𝟙 S) (a : Pic X) :
    (relativeKernelEquiv f e he (relativeClass f a)).val = normalize f e a := rfl

/-- Two classes differ by a base twist exactly when their normalizations agree. -/
theorem relativeClass_eq_iff_normalize_eq (he : e ≫ f = 𝟙 S) (a b : Pic X) :
    relativeClass f a = relativeClass f b ↔ normalize f e a = normalize f e b := by
  rw [← (relativeKernelEquiv f e he).injective.eq_iff, Subtype.ext_iff]
  rfl

end FLT.Mazur.SchemePicard
