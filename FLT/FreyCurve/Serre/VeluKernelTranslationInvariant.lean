/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluCofiniteFunctionEquality

/-!
# Original generic Vélu coordinates are invariant under kernel translation

The original finite sums are constant on kernel cosets. Specializing the
original rational formulas on a cofinite set identifies their translates in
the original quadratic function field over an algebraically closed field.
-/

@[expose] public noncomputable section

open RatFunc

namespace WeierstrassCurve.Velu

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

omit [CharZero K] [E.IsElliptic] [Fintype G] in
/-- Outside finitely many abscissae every original affine point avoids the kernel. -/
theorem eventually_affinePoint_not_mem_kernel [Finite G] :
    ∀ᶠ x in Filter.cofinite, ∀ y (hP : E.toAffine.Nonsingular x y),
      Affine.Point.some x y hP ∉ G := by
  let _ := Fintype.ofFinite G
  filter_upwards [(Finset.univ.image (fun Q : G => xCoord Q.val)).eventually_cofinite_notMem]
    with x hx y hP hmem
  exact hx (Finset.mem_image.mpr ⟨⟨.some x y hP, hmem⟩, Finset.mem_univ _, rfl⟩)

include hodd

/-- The translated rational coordinates and original coordinates have the same geometric values. -/
theorem translated_image_kernel_cofinite {u v : K} (hQ : E.toAffine.Nonsingular u v)
    (hQG : Affine.Point.some u v hQ ∈ G) :
    ∀ᶠ x in Filter.cofinite, ∀ y, E.toAffine.Equation x y →
      affineValue E x y (imageX E G (substitution _ (translateX_transcendental E hQ))) =
        affineValue E x y (liftX E (xFunction E G)) ∧
      affineValue E x y
          (imageY E G (substitution _ (translateX_transcendental E hQ)) (translateY E u v)) =
        affineValue E x y (liftY E (curve E G) (xFunction E G) (slopeFunction E G)) := by
  have htr := eventuallyValue_translate E u v
  have hix := htr.1.substitution E (translateX_transcendental E hQ) (xFunction E G)
  have hiy := eventuallyValue_imageY E G htr.1 htr.2 (translateX_transcendental E hQ)
  filter_upwards [hix, hiy, Filter.eventually_cofinite_ne u,
    eventually_affinePoint_not_mem_kernel E G] with x hix hiy hxu hn y hy
  have hP := Affine.equation_iff_nonsingular.mp hy
  have hPG := hn y hP
  have hSG : Affine.Point.some x y hP + Affine.Point.some u v hQ ∉ G := by
    intro h
    exact hPG (by simpa using G.sub_mem h hQG)
  have hs : E.toAffine.Nonsingular
      (E.toAffine.addX x u ((y - v) / (x - u)))
      (E.toAffine.addY x u y ((y - v) / (x - u))) := by
    simpa only [Affine.slope_of_X_ne hxu] using
      Affine.nonsingular_add hP hQ (fun hh => hxu hh.1)
  have hsum : Affine.Point.some x y hP + Affine.Point.some u v hQ =
      Affine.Point.some _ _ hs := by
    simp only [Affine.Point.add_of_X_ne hxu, Affine.slope_of_X_ne hxu]
  have hsv := rational_values_eq_maps E G hodd hs (by rwa [← hsum])
  have hpv := affineValue_velu E G hodd hP hPG
  change affineValue E x y (substitution _ (translateX_transcendental E hQ)
    (xFunction E G)) = _ ∧ _
  rw [hix y hy, hiy y hy]
  rw [hsv.2, hsv.1, hpv.1, hpv.2, ← hsum]
  exact ⟨xMap_add E G _ ⟨_, hQG⟩, yMap_add E G _ ⟨_, hQG⟩⟩

variable [IsAlgClosed K]

/-- Original generic Vélu x and y are unchanged by an original kernel translation. -/
theorem translated_image_kernel {u v : K} (hQ : E.toAffine.Nonsingular u v)
    (hQG : Affine.Point.some u v hQ ∈ G) :
    imageX E G (substitution _ (translateX_transcendental E hQ)) =
        liftX E (xFunction E G) ∧
      imageY E G (substitution _ (translateX_transcendental E hQ)) (translateY E u v) =
        liftY E (curve E G) (xFunction E G) (slopeFunction E G) := by
  have h := translated_image_kernel_cofinite E G hodd hQ hQG
  constructor
  · apply functionField_eq_of_cofinite E
    filter_upwards [h] with x hx y hy
    exact (hx y hy).1
  · apply functionField_eq_of_cofinite E
    filter_upwards [h] with x hx y hy
    exact (hx y hy).2

end WeierstrassCurve.Velu
