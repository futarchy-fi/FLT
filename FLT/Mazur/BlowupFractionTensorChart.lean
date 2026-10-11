/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupFractionPrincipalIdeal
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Original center and regular denominator on actual product charts

These are tensor products of the original fraction chart with a flat factor,
not fraction charts formed after an arbitrary base change. The original
denominator remains regular; the full pulled-back ideal is its principal ideal.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.BlowupFractionChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (f : A) (S : Type*) [CommRing S] [Algebra R S]

/-- The genuine tensor chart of the modified input and the other factor. -/
def ProductChart := chart I f ⊗[R] S

instance productChartCommRing : CommRing (ProductChart (R := R) I f S) :=
  inferInstanceAs (CommRing (chart I f ⊗[R] S))

instance productChartAlgebra : Algebra (chart I f) (ProductChart (R := R) I f S) :=
  inferInstanceAs (Algebra (chart I f) (chart I f ⊗[R] S))

instance productChartFlat [Module.Flat R S] :
    Module.Flat (chart I f) (ProductChart (R := R) I f S) :=
  inferInstanceAs (Module.Flat (chart I f) (chart I f ⊗[R] S))

/-- The original input functions on the genuine tensor chart. -/
irreducible_def productOriginal : A →+* ProductChart (R := R) I f S :=
  (algebraMap (chart I f) _).comp (algebraMap A (chart I f))

/-- The original denominator is retained as the actual first-factor tensor. -/
theorem productOriginal_denominator :
    productOriginal (R := R) I f S f = denominator I f ⊗ₜ[R] (1 : S) := by
  rw [productOriginal_def]
  rfl

/-- The complete center becomes the original principal denominator ideal on the product. -/
theorem productOriginal_center (hf : f ∈ I) :
    I.map (productOriginal (R := R) I f S) =
      Ideal.span {productOriginal (R := R) I f S f} := by
  rw [productOriginal_def]
  exact center_map_eq_mapped_denominator I f hf (B := ProductChart (R := R) I f S)
    (algebraMap (chart I f) (ProductChart (R := R) I f S))

/-- Flatness of the other factor proves denominator regularity on the actual product chart. -/
theorem productOriginal_regular [Module.Flat R S] :
    IsRegular (productOriginal (R := R) I f S f) := by
  rw [productOriginal_def]
  exact flat_denominator_regular I f (B := ProductChart (R := R) I f S)

/-- Every localization of the genuine product retains the full principalized center. -/
theorem localized_productOriginal_center (hf : f ∈ I)
    {T : Type*} [CommRing T] (ψ : ProductChart (R := R) I f S →+* T) :
    I.map (ψ.comp (productOriginal (R := R) I f S)) =
      Ideal.span {ψ (productOriginal (R := R) I f S f)} := by
  rw [← Ideal.map_map, productOriginal_center I f S hf,
    Ideal.map_span, Set.image_singleton]

/-- Original denominators stay regular on all localized flat-product charts. -/
theorem localized_productOriginal_regular [Module.Flat R S]
    (M : Submonoid (ProductChart (R := R) I f S))
    (T : Type*) [CommRing T] [Algebra (ProductChart (R := R) I f S) T]
    [IsLocalization M T] :
    IsRegular (algebraMap (ProductChart (R := R) I f S) T
      (productOriginal (R := R) I f S f)) := by
  let _ := IsLocalization.flat T M
  exact regular_algebraMap_of_flat (A := ProductChart (R := R) I f S) (B := T) _
    (productOriginal_regular (R := R) I f S)

end FLT.Mazur.BlowupFractionChart
