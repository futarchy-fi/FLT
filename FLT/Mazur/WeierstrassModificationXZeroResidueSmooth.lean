/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXZeroResidue
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smoothness of the entire start-zero residue chart

The full tensor algebra is a localized polynomial line. This proves its
smoothness over the residue field without claiming that it is the whole
global smooth identity component.
-/

@[expose] public noncomputable section
open Polynomial IsLocalRing AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX

/-- The full slope open is smooth over any coefficient ring. -/
theorem slopeOpen_smooth {R : Type*} [CommRing R] (a : R) : Algebra.Smooth R (SlopeOpen a) := by
  let _ : Algebra.Smooth R R[X] := { }
  let _ : Algebra.Smooth R[X] (SlopeOpen a) :=
    Algebra.Smooth.of_isLocalization_Away (slopePolynomial a)
  exact Algebra.Smooth.comp R R[X] (SlopeOpen a)

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth) (k : ℕ) (hk : k = 0) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
local notation "K" => ResidueField R
local notation "T" => ScalarExtension W (π ^ k) b3 b4 b6 K

include D hdepth hk h3 h4 h6

/-- The entire original start-zero tensor residue algebra is smooth. -/
theorem zeroResidueTensor_smooth : Algebra.Smooth K T := by
  let _ := slopeOpen_smooth (residue R W.a₁)
  exact Algebra.Smooth.of_equiv
    (zeroResidueSlopeEquiv D hdepth k hk b3 b4 b6 h3 h4 h6).symm

/-- Its original structure morphism to the residue field is smooth. -/
theorem zeroResidueTensor_structure_smooth :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap K T))) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  exact RingHom.smooth_algebraMap.mpr
    (zeroResidueTensor_smooth D hdepth k hk b3 b4 b6 h3 h4 h6)

end FLT.Mazur.WeierstrassModificationX
