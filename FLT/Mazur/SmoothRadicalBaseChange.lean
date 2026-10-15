/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothGeometricallyReduced
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Smooth extension preserves radical ideals over Noetherian rings

The quotient base is reduced even when the original coefficient ring has
nilpotents. Smooth base change is geometrically reduced and flat, so its
actual quotient algebra is reduced. Thus extension preserves the exact
radical ideal, rather than just its vanishing set.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.Approximation
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- A smooth algebra over a reduced Noetherian ring is reduced. -/
theorem isReduced_of_smooth_noetherian [IsNoetherianRing R] [_root_.IsReduced R]
    [Algebra.Smooth R B] : _root_.IsReduced B := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have hf : Smooth f := HasRingHomProperty.Spec_iff.mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)
  let _ := hf
  let _ := geometricallyReduced_of_smooth f
  exact (affine_isReduced_iff (.of B)).mp
    (GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f)

/-- Smooth extension of a radical ideal is radical, including over nonreduced bases. -/
theorem radical_map_of_smooth [IsNoetherianRing R] [Algebra.Smooth R B]
    (I : Ideal R) (hI : I.IsRadical) : (I.map (algebraMap R B)).IsRadical := by
  let _ : _root_.IsReduced (R ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hI
  let _ : _root_.IsReduced ((R ⧸ I) ⊗[R] B) :=
    isReduced_of_smooth_noetherian (R ⧸ I) ((R ⧸ I) ⊗[R] B)
  apply (Ideal.isRadical_iff_quotient_reduced _).mpr
  exact isReduced_of_injective
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toRingHom
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).injective

end FLT.Mazur.Approximation
