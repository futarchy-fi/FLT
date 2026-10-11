/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RegularCenterConormalQuotient

/-!
# Linear combinations and image ideals of actual center quotients

Regularity identifies the quotient of each original branch linear form and
compares the quotient before and after mapping the center ideal. These are
identities before residue restriction, where cancellation is legitimate.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.RegularCenter
variable {A S B : Type*} [CommRing A] [CommRing S] [CommRing B]
  (I : Ideal A) (φ : A →+* B) (z : B) (hI : I.map φ = Ideal.span {z})
  (hz : IsRegular z)

include hz in
/-- Division by the retained regular denominator preserves every branch linear form. -/
theorem quotient_add_mul (x y a : A) (hx : x ∈ I) (hy : y ∈ I) :
    quotient I φ z hI (y + a * x) (I.add_mem hy (I.mul_mem_left a hx)) =
      quotient I φ z hI y hy + φ a * quotient I φ z hI x hx := by
  symm
  apply quotient_unique I φ z hI hz
  rw [mul_add, denominator_mul_quotient, mul_left_comm z,
    denominator_mul_quotient, map_add, map_mul]

variable (f : A →+* S) (g : S →+* B)
  (h : (I.map f).map g = Ideal.span {z})

include h in
/-- Mapping the center before principalizing it retains the same full ideal. -/
theorem quotient_image_center : I.map (g.comp f) = Ideal.span {z} := by
  rw [← Ideal.map_map, h]

include hz in
/-- The quotient of an original generator agrees with its quotient in the mapped center. -/
theorem quotient_image (a : A) (ha : a ∈ I) :
    quotient (I.map f) g z h (f a) (Ideal.mem_map_of_mem f ha) =
      quotient I (g.comp f) z (quotient_image_center I z f g h) a ha := by
  apply quotient_unique I (g.comp f) z _ hz
  exact denominator_mul_quotient (I.map f) g z h (f a) (Ideal.mem_map_of_mem f ha)

end FLT.Mazur.RegularCenter
