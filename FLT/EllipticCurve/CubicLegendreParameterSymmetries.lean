/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreJFinite
public import FLT.EllipticCurve.CubicLegendreSymmetries
/-! # Integral automorphisms of the Legendre parameter chart

The transformations λ ↦ 1-λ and λ ↦ λ⁻¹ are actual involutions of
the localized parameter ring. Their local curve isomorphisms prove
invariance of j by faithfully flat descent. They are therefore
automorphisms over the integral j-line, and satisfy the braid relation.
-/

@[expose] public noncomputable section
open Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts

section JInvariance
universe u
private theorem elliptic_j_congr {A : Type u} [CommRing A]
    {V W : WeierstrassCurve A} [V.IsElliptic] [W.IsElliptic] (h : V = W) :
    V.j = W.j := by
  subst W
  rfl

variable {R : Type u} [CommRing R] [Nontrivial R] [Fact (IsUnit (2 : R))]

/-- The integral swap preserves j, detected on its faithful quadratic cover. -/
theorem legendreSwap_j (l : R)
    [(legendreCurve l).IsElliptic] [(legendreCurve (1 - l)).IsElliptic] :
    (legendreCurve (1 - l)).j = (legendreCurve l).j := by
  apply FaithfulSMul.algebraMap_injective R (LegendreSwapRing R)
  rw [← WeierstrassCurve.map_j, ← WeierstrassCurve.map_j]
  simp only [legendreCurve_map, map_sub, map_one]
  have : (legendreCurve (algebraMap R (LegendreSwapRing R) l)).IsElliptic := by
    rw [← legendreCurve_map]
    infer_instance
  have hu : (quadraticEtaleUnit (-1 : Rˣ) : LegendreSwapRing R) ^ 2 = -1 := by
    simpa only [Units.val_neg, Units.val_one, map_neg, map_one] using
      quadraticEtaleUnit_square (-1 : Rˣ)
  have h := WeierstrassCurve.variableChange_j
    (legendreCurve (algebraMap R (LegendreSwapRing R) l))
    (legendreSwapChange (quadraticEtaleUnit (-1 : Rˣ)))
  simpa only [legendreSwapChange_curve _ _ hu] using h

/-- The integral reciprocal transformation preserves j. -/
theorem legendreReciprocal_j (l : Rˣ)
    [(legendreCurve (l : R)).IsElliptic]
    [(legendreCurve ((l⁻¹ : Rˣ) : R)).IsElliptic] :
    (legendreCurve ((l⁻¹ : Rˣ) : R)).j = (legendreCurve (l : R)).j := by
  apply FaithfulSMul.algebraMap_injective R (LegendreReciprocalRing l)
  rw [← WeierstrassCurve.map_j, ← WeierstrassCurve.map_j]
  simp only [legendreCurve_map]
  let l' : (LegendreReciprocalRing l)ˣ :=
    Units.map (algebraMap R (LegendreReciprocalRing l)) l
  have : (legendreCurve (l' : LegendreReciprocalRing l)).IsElliptic := by
    change (legendreCurve (algebraMap R (LegendreReciprocalRing l) (l : R))).IsElliptic
    rw [← legendreCurve_map]
    infer_instance
  have h := WeierstrassCurve.variableChange_j (legendreCurve (l' : LegendreReciprocalRing l))
    (legendreReciprocalChange (quadraticEtaleUnit l))
  have he : legendreCurve (algebraMap R (LegendreReciprocalRing l) ((l⁻¹ : Rˣ) : R)) =
      legendreReciprocalChange (quadraticEtaleUnit l) •
        legendreCurve (l' : LegendreReciprocalRing l) := by
    have hv : ((l'⁻¹ : (LegendreReciprocalRing l)ˣ) : LegendreReciprocalRing l) =
        algebraMap R (LegendreReciprocalRing l) ((l⁻¹ : Rˣ) : R) := rfl
    have he' := (legendreReciprocalChange_curve l' _ (quadraticEtaleUnit_square l)).symm
    rw [hv] at he'
    exact he'
  have : (legendreCurve (algebraMap R (LegendreReciprocalRing l)
      ((l⁻¹ : Rˣ) : R))).IsElliptic := by
    rw [← legendreCurve_map]
    infer_instance
  exact (elliptic_j_congr he).trans h


end JInvariance

/-- A homomorphism from the Legendre chart is determined by its parameter. -/
theorem legendreRingHom_ext {S : Type*} [CommRing S] (p : ℕ)
    (f g : LegendreBase p →+* S) (h : f (legendreParameter p) = g (legendreParameter p)) :
    f = g :=
  (legendreParameterEquiv p S).injective (Subtype.ext h)

/-- The universal nonsingular parameter as a unit. -/
def legendreParameterUnit (p : ℕ) : (LegendreBase p)ˣ := (legendreBase_units p).2.2.1.unit

/-- The distinguished unit has value equal to the universal parameter. -/
@[simp] theorem legendreParameterUnit_val (p : ℕ) :
    (legendreParameterUnit p : LegendreBase p) = legendreParameter p :=
  IsUnit.unit_spec _

/-- The swapped parameter and its difference from one are units. -/
theorem legendreSwapParameter_units (p : ℕ) :
    IsUnit (1 - legendreParameter p) ∧ IsUnit ((1 - legendreParameter p) - 1) := by
  constructor
  · simpa only [neg_sub] using (legendreBase_units p).2.2.2.neg
  · simpa using (legendreBase_units p).2.2.1.neg

/-- The integral substitution λ ↦ 1-λ. -/
def legendreSwapParameterMap (p : ℕ) : LegendreBase p →+* LegendreBase p :=
  legendreSpecialize p (1 - legendreParameter p)
    (legendreBase_units p).1 (legendreBase_units p).2.1
    (legendreSwapParameter_units p).1 (legendreSwapParameter_units p).2

/-- The swap has its stated value on the universal parameter. -/
@[simp] theorem legendreSwapParameterMap_parameter (p : ℕ) :
    legendreSwapParameterMap p (legendreParameter p) = 1 - legendreParameter p :=
  legendreSpecialize_parameter _ _ _ _ _ _

/-- Swapping the parameter twice is the identity. -/
theorem legendreSwapParameterMap_involutive (p : ℕ) :
    Function.Involutive (legendreSwapParameterMap p) := by
  have h : (legendreSwapParameterMap p).comp (legendreSwapParameterMap p) = RingHom.id _ := by
    apply legendreRingHom_ext p
    simp
  intro x
  exact DFunLike.congr_fun h x

/-- The swap as an automorphism of the coefficient ring. -/
def legendreSwapParameterEquiv (p : ℕ) : LegendreBase p ≃+* LegendreBase p where
  __ := legendreSwapParameterMap p
  invFun := legendreSwapParameterMap p
  left_inv := legendreSwapParameterMap_involutive p
  right_inv := legendreSwapParameterMap_involutive p

/-- The reciprocal parameter and its difference from one are units. -/
theorem legendreReciprocalParameter_units (p : ℕ) :
    IsUnit (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p) ∧
      IsUnit (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) - (1 : LegendreBase p)) := by
  constructor
  · exact Units.isUnit _
  · have h : (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p) - 1 =
        -(((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p) *
          (legendreParameter p - 1) := by
      have hi := (legendreParameterUnit p).inv_mul
      rw [legendreParameterUnit_val] at hi
      linear_combination hi
    rw [h]
    exact (Units.isUnit _).neg.mul (legendreBase_units p).2.2.2

/-- The integral substitution λ ↦ λ⁻¹. -/
def legendreReciprocalParameterMap (p : ℕ) : LegendreBase p →+* LegendreBase p :=
  legendreSpecialize p ((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ)
    (legendreBase_units p).1 (legendreBase_units p).2.1
    (legendreReciprocalParameter_units p).1 (legendreReciprocalParameter_units p).2

/-- The reciprocal substitution has its stated value on the parameter. -/
@[simp] theorem legendreReciprocalParameterMap_parameter (p : ℕ) :
    legendreReciprocalParameterMap p (legendreParameter p) =
      ((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) :=
  legendreSpecialize_parameter _ _ _ _ _ _

/-- Taking the reciprocal twice is the identity. -/
theorem legendreReciprocalParameterMap_involutive (p : ℕ) :
    Function.Involutive (legendreReciprocalParameterMap p) := by
  have h : (legendreReciprocalParameterMap p).comp (legendreReciprocalParameterMap p) =
      RingHom.id _ := by
    apply legendreRingHom_ext p
    change legendreReciprocalParameterMap p (legendreReciprocalParameterMap p
      (legendreParameter p)) = legendreParameter p
    rw [legendreReciprocalParameterMap_parameter]
    have hi := (legendreParameterUnit p).mul_inv
    have hm := congrArg (legendreReciprocalParameterMap p) hi
    rw [map_mul, map_one, legendreParameterUnit_val,
      legendreReciprocalParameterMap_parameter] at hm
    rw [legendreParameterUnit_val] at hi
    linear_combination (legendreParameter p) * hm -
      (legendreReciprocalParameterMap p
        (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)) * hi
  intro x
  exact DFunLike.congr_fun h x

/-- The reciprocal substitution as an automorphism. -/
def legendreReciprocalParameterEquiv (p : ℕ) : LegendreBase p ≃+* LegendreBase p where
  __ := legendreReciprocalParameterMap p
  invFun := legendreReciprocalParameterMap p
  left_inv := legendreReciprocalParameterMap_involutive p
  right_inv := legendreReciprocalParameterMap_involutive p


/-- Two is invertible in the universal parameter ring. -/
instance legendreBaseTwoUnit (p : ℕ) : Fact (IsUnit (2 : LegendreBase p)) :=
  ⟨(legendreBase_units p).1⟩

/-- The swapped universal Legendre equation is elliptic. -/
instance legendreSwapCurveElliptic (p : ℕ) :
    (legendreCurve (1 - legendreParameter p)).IsElliptic :=
  legendreCurve_elliptic _ (legendreBase_units p).1
    (legendreSwapParameter_units p).1 (legendreSwapParameter_units p).2

/-- The reciprocal universal Legendre equation is elliptic. -/
instance legendreReciprocalCurveElliptic (p : ℕ) :
    (legendreCurve
      (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)).IsElliptic :=
  legendreCurve_elliptic _ (legendreBase_units p).1
    (legendreReciprocalParameter_units p).1 (legendreReciprocalParameter_units p).2

/-- The coefficient swap fixes the universal j-invariant. -/
theorem legendreSwapParameterMap_j (p : ℕ) [NeZero p] :
    legendreSwapParameterMap p (legendreModel p).j = (legendreModel p).j := by
  have : (legendreCurve (legendreParameter p)).IsElliptic := legendreModelElliptic p
  have hj := legendreSwap_j (legendreParameter p)
  have he : (legendreModel p).map (legendreSwapParameterMap p) =
      legendreCurve (1 - legendreParameter p) :=
    legendreModel_specialize _ _ _ _ _ _
  rw [← WeierstrassCurve.map_j]
  exact (elliptic_j_congr he).trans hj

/-- The coefficient reciprocal substitution fixes the universal j-invariant. -/
theorem legendreReciprocalParameterMap_j (p : ℕ) [NeZero p] :
    legendreReciprocalParameterMap p (legendreModel p).j = (legendreModel p).j := by
  have : (legendreCurve (legendreParameterUnit p : LegendreBase p)).IsElliptic := by
    simpa only [legendreParameterUnit_val, legendreModel] using (legendreModelElliptic p)
  have hj := legendreReciprocal_j (legendreParameterUnit p)
  have he : (legendreModel p).map (legendreReciprocalParameterMap p) =
      legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p) :=
    legendreModel_specialize _ _ _ _ _ _
  rw [← WeierstrassCurve.map_j]
  apply (elliptic_j_congr he).trans
  simpa only [legendreParameterUnit_val, legendreModel] using hj

/-- Fixing j makes a parameter endomorphism linear over the j-line. -/
theorem legendreParameterMap_comp_jMap (p : ℕ) (f : LegendreBase p →+* LegendreBase p)
    (hj : f (legendreModel p).j = (legendreModel p).j) :
    f.comp (legendreJMap p) = legendreJMap p := by
  apply Polynomial.ringHom_ext'
  · apply IsLocalization.ringHom_ext (Submonoid.powers (2 * (p : ℤ)))
    exact Subsingleton.elim _ _
  · simpa only [RingHom.comp_apply, legendreJMap, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X] using hj

/-- The swap as an automorphism over the integral j-line. -/
def legendreSwapParameterAlgEquiv (p : ℕ) [NeZero p] :
    LegendreBase p ≃ₐ[LegendreJBase p] LegendreBase p where
  __ := legendreSwapParameterEquiv p
  commutes' x := DFunLike.congr_fun
    (legendreParameterMap_comp_jMap p (legendreSwapParameterMap p)
      (legendreSwapParameterMap_j p)) x

/-- The reciprocal substitution as an automorphism over the integral j-line. -/
def legendreReciprocalParameterAlgEquiv (p : ℕ) [NeZero p] :
    LegendreBase p ≃ₐ[LegendreJBase p] LegendreBase p where
  __ := legendreReciprocalParameterEquiv p
  commutes' x := DFunLike.congr_fun
    (legendreParameterMap_comp_jMap p (legendreReciprocalParameterMap p)
      (legendreReciprocalParameterMap_j p)) x


attribute [local irreducible] legendreSwapParameterMap legendreReciprocalParameterMap

/-- The two parameter involutions satisfy the braid relation. -/
theorem legendreParameterMaps_braid (p : ℕ) [NeZero p] :
    ((legendreSwapParameterMap p).comp (legendreReciprocalParameterMap p)).comp
        (legendreSwapParameterMap p) =
      ((legendreReciprocalParameterMap p).comp (legendreSwapParameterMap p)).comp
        (legendreReciprocalParameterMap p) := by
  apply legendreRingHom_ext p
  let K := FractionRing (LegendreBase p)
  let ι : LegendreBase p →+* K := algebraMap _ _
  apply FaithfulSMul.algebraMap_injective (LegendreBase p) K
  have hι0 : ι (legendreParameter p) ≠ 0 :=
    ((legendreBase_units p).2.2.1.map ι).ne_zero
  have hι1 : ι (legendreParameter p) ≠ 1 := by
    have h := ((legendreBase_units p).2.2.2.map ι).ne_zero
    simpa only [map_sub, map_one, sub_ne_zero] using h
  have hs : ι (legendreSwapParameterMap p
      (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)) =
      (1 - ι (legendreParameter p))⁻¹ := by
    simpa only [RingHom.comp_apply, legendreParameterUnit_val,
      legendreSwapParameterMap_parameter, map_sub, map_one] using
      (map_units_inv (ι.comp (legendreSwapParameterMap p)) (legendreParameterUnit p))
  have hts : ι (legendreReciprocalParameterMap p (legendreSwapParameterMap p
      (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))) =
      (1 - (ι (legendreParameter p))⁻¹)⁻¹ := by
    have ht := map_units_inv ((ι.comp (legendreReciprocalParameterMap p)).comp
      (legendreSwapParameterMap p)) (legendreParameterUnit p)
    change ι (legendreReciprocalParameterMap p (legendreSwapParameterMap p
      (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))) =
      (ι (legendreReciprocalParameterMap p (legendreSwapParameterMap p
        (legendreParameterUnit p : LegendreBase p))))⁻¹ at ht
    rw [legendreParameterUnit_val, legendreSwapParameterMap_parameter, map_sub,
      map_one, legendreReciprocalParameterMap_parameter, map_sub, map_one,
      map_units_inv ι (legendreParameterUnit p), legendreParameterUnit_val] at ht
    exact ht
  change ι (legendreSwapParameterMap p (legendreReciprocalParameterMap p
      (legendreSwapParameterMap p (legendreParameter p)))) =
    ι (legendreReciprocalParameterMap p (legendreSwapParameterMap p
      (legendreReciprocalParameterMap p (legendreParameter p))))
  rw [legendreSwapParameterMap_parameter, map_sub, map_one,
    legendreReciprocalParameterMap_parameter, map_sub, map_one, map_sub, map_one, hs, hts]
  have h1 : 1 - ι (legendreParameter p) ≠ 0 := sub_ne_zero.mpr hι1.symm
  change (1 : K) - (1 - ι (legendreParameter p))⁻¹ =
    (1 - (ι (legendreParameter p))⁻¹)⁻¹
  have h2 : 1 - (ι (legendreParameter p))⁻¹ ≠ 0 := by
    intro h
    have he : (ι (legendreParameter p))⁻¹ = 1 := (sub_eq_zero.mp h).symm
    exact hι1 (inv_eq_one.mp he)
  apply (mul_eq_one_iff_eq_inv₀ h2).mp
  linear_combination
    (ι (legendreParameter p))⁻¹ * (mul_inv_cancel₀ h1) +
      (1 - ι (legendreParameter p))⁻¹ * (mul_inv_cancel₀ hι0)

end WeierstrassCurve.CubicCharts
