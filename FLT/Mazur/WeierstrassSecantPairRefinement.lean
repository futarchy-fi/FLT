/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryPairPresentation

/-!
# An actual secant refinement of an affine pair

Localizing the difference of the two abscissae constructs an ordinary addition
presentation. Every residue map sending the second abscissa to zero and the
first to a unit factors through this open. Thus this refinement retains the
entire smooth affine parameter over a nodal input, over arbitrary residue rings.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (a c : Coordinate W 2 →ₐ[R] S)

/-- The actual secant principal open of the given pair. -/
abbrev SecantPairRing := Localization.Away (a (coord W 2 0) - c (coord W 2 0))

local notation "T" => SecantPairRing W a c
local notation "j" => IsScalarTower.toAlgHom R S T

/-- The localized pair has invertible secant denominator. -/
theorem secantPair_denominator :
    IsUnit (chartProductEvaluation W 2 2 ((j).comp a) ((j).comp c)
      (if false then tangentDenominator W else secantDenominator W)) := by
  let f : AffineProduct W →ₐ[R] T :=
    chartProductEvaluation W 2 2 ((j).comp a) ((j).comp c)
  have hl : f.comp (productLeft W) = (j).comp a :=
    chartProductEvaluation_left W 2 2 ((j).comp a) ((j).comp c)
  have hr : f.comp (productRight W) = (j).comp c :=
    chartProductEvaluation_right W 2 2 ((j).comp a) ((j).comp c)
  change IsUnit (f (secantDenominator W))
  rw [map_secantDenominator]
  simp only [productX₁, productX₂, ← AlgHom.comp_apply, hl, hr]
  change IsUnit (algebraMap S T (a (coord W 2 0)) - algebraMap S T (c (coord W 2 0)))
  rw [← map_sub]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The ordinary addition presentation on this concrete principal open. -/
def secantPairPresentation : additionChartRing W (ordinaryIndex false) →ₐ[R] T :=
  ordinaryPairPresentation W ((j).comp a) ((j).comp c) false (secantPair_denominator W a c)

/-- The secant refinement retains the original left point. -/
theorem secantPairPresentation_left :
    (secantPairPresentation W a c).comp (ordinaryInputLeft W false) = (j).comp a :=
  ordinaryPairPresentation_left ..

/-- The secant refinement retains the original right point. -/
theorem secantPairPresentation_right :
    (secantPairPresentation W a c).comp (ordinaryInputRight W false) = (j).comp c :=
  ordinaryPairPresentation_right ..

variable {C : Type*} [CommRing C] (e : S →+* C)
  (hx : IsUnit (e (a (coord W 2 0)))) (hc : e (c (coord W 2 0)) = 0)

include hx hc in
/-- Every smooth affine by node residue lies in the actual secant open. -/
theorem secantPair_residue_denominator :
    IsUnit (e (a (coord W 2 0) - c (coord W 2 0))) := by
  rw [map_sub, hc, sub_zero]
  exact hx

/-- The residue factorization is constructed by the localization universal property. -/
def secantPairResidue : T →+* C :=
  IsLocalization.Away.lift (a (coord W 2 0) - c (coord W 2 0))
    (secantPair_residue_denominator W a c e hx hc)

/-- Its contraction is the original residue map on every element. -/
@[simp] theorem secantPairResidue_base (t : S) :
    secantPairResidue W a c e hx hc (algebraMap S T t) = e t :=
  IsLocalization.Away.lift_eq _ _ _

/-- The actual left input is unchanged after residue factorization. -/
@[simp] theorem secantPairResidue_left (t : Coordinate W 2) :
    secantPairResidue W a c e hx hc
      (secantPairPresentation W a c (ordinaryInputLeft W false t)) = e (a t) := by
  have h := DFunLike.congr_fun (secantPairPresentation_left W a c) t
  change secantPairPresentation W a c (ordinaryInputLeft W false t) = algebraMap S T (a t)
    at h
  rw [h, secantPairResidue_base]

/-- The actual right input is unchanged after residue factorization. -/
@[simp] theorem secantPairResidue_right (t : Coordinate W 2) :
    secantPairResidue W a c e hx hc
      (secantPairPresentation W a c (ordinaryInputRight W false t)) = e (c t) := by
  have h := DFunLike.congr_fun (secantPairPresentation_right W a c) t
  change secantPairPresentation W a c (ordinaryInputRight W false t) = algebraMap S T (c t)
    at h
  rw [h, secantPairResidue_base]

end FLT.Mazur.WeierstrassIntegralChart
