/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreMonic
public import FLT.EllipticCurve.CubicLegendreParameters
public import Mathlib.RingTheory.FiniteType

/-! # The finite flat Legendre cover of the j-line

Over ℤ[1/(2p)], the integral Legendre parameter ring is the algebra
obtained by adjoining a root of the monic degree-six j-relation.
The explicit two-sided presentation gives a free module of rank six
for nonzero level. The Legendre map and its prime cyclic parameter
cover are finite, flat and surjective.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts

/-- The coefficient ring with two and the level inverted. -/
abbrev LegendreConstants (p : ℕ) : Type := Localization.Away (2 * (p : ℤ))
/-- The affine j-line over the level coefficient ring. -/
abbrev LegendreJBase (p : ℕ) : Type := (LegendreConstants p)[X]

instance legendreConstantsDomain (p : ℕ) [NeZero p] : IsDomain (LegendreConstants p) :=
  Localization.Away.isDomain (mul_ne_zero (by norm_num) (by exact_mod_cast NeZero.ne p))

instance legendreJBaseDomain (p : ℕ) [NeZero p] : IsDomain (LegendreJBase p) := by
  have := legendreConstantsDomain p
  infer_instance

/-- Two and the level are units in the coefficient ring. -/
theorem legendreConstants_units (p : ℕ) :
    IsUnit (2 : LegendreConstants p) ∧ IsUnit (p : LegendreConstants p) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := LegendreConstants p) (2 * (p : ℤ))
  simpa only [map_mul, map_ofNat, map_natCast, IsUnit.mul_iff] using h

/-- Two and the level remain units on the j-line. -/
theorem legendreJBase_units (p : ℕ) :
    IsUnit (2 : LegendreJBase p) ∧ IsUnit (p : LegendreJBase p) :=
  ⟨by simpa only [map_ofNat] using (legendreConstants_units p).1.map C,
   by simpa only [map_natCast] using (legendreConstants_units p).2.map C⟩

/-- The coefficient specialization into the integral Legendre chart. -/
def legendreConstantMap (p : ℕ) : LegendreConstants p →+* LegendreBase p :=
  IsLocalization.Away.lift (2 * (p : ℤ))
    (show IsUnit ((Int.castRingHom (LegendreBase p)) (2 * (p : ℤ))) by
      simpa only [map_mul, map_ofNat, Int.coe_castRingHom, Int.cast_natCast] using
        (legendreBase_units p).1.mul (legendreBase_units p).2.1)

/-- The ring map sending the j-coordinate to the actual curve invariant. -/
def legendreJMap (p : ℕ) : LegendreJBase p →+* LegendreBase p :=
  eval₂RingHom (legendreConstantMap p) (legendreModel p).j

instance legendreJAlgebra (p : ℕ) : Algebra (LegendreJBase p) (LegendreBase p) :=
  (legendreJMap p).toAlgebra

instance legendreJModule (p : ℕ) : Module (LegendreJBase p) (LegendreBase p) :=
  @Algebra.toModule (LegendreJBase p) (LegendreBase p) _ _ (legendreJAlgebra p)

/-- The normalized coordinate j/256. -/
def legendreJScaled (p : ℕ) : LegendreJBase p :=
  X * Ring.inverse 256

/-- Multiplication by 256 recovers the j-coordinate. -/
theorem legendreJScaled_spec (p : ℕ) :
    256 * legendreJScaled p = (X : LegendreJBase p) := by
  have hu : IsUnit (256 : LegendreJBase p) := by
    convert (legendreJBase_units p).1.pow 8 using 1
    norm_num
  unfold legendreJScaled
  calc
    256 * (X * Ring.inverse 256) = X * (256 * Ring.inverse 256) := by ring
    _ = X := by rw [Ring.mul_inverse_cancel _ hu, mul_one]

/-- Specialization sends normalized j to the normalized curve invariant. -/
theorem legendreJMap_scaled (p : ℕ) :
    256 * legendreJMap p (legendreJScaled p) = (legendreModel p).j := by
  have h := congrArg (legendreJMap p) (legendreJScaled_spec p)
  simpa only [map_mul, map_ofNat, legendreJMap, coe_eval₂RingHom, eval₂_X] using h

/-- The finite monic presentation over the j-line. -/
abbrev LegendreJRoot (p : ℕ) : Type :=
  AdjoinRoot (legendreMonicPolynomial (legendreJScaled p))

/-- The universal root satisfies the normalized Legendre relation. -/
theorem legendreJRoot_equation (p : ℕ) :
    (legendreMonicPolynomial
      (AdjoinRoot.of (legendreMonicPolynomial (legendreJScaled p)) (legendreJScaled p))).eval
      (AdjoinRoot.root (legendreMonicPolynomial (legendreJScaled p))) = 0 := by
  rw [legendreMonicPolynomial_eval]
  have h := AdjoinRoot.eval₂_root (legendreMonicPolynomial (legendreJScaled p))
  rw [legendreMonicPolynomial_eval₂] at h
  exact h

/-- The universal root and its difference from one are units. -/
theorem legendreJRoot_units (p : ℕ) :
    IsUnit (AdjoinRoot.root (legendreMonicPolynomial (legendreJScaled p))) ∧
      IsUnit (AdjoinRoot.root (legendreMonicPolynomial (legendreJScaled p)) - 1) :=
  ⟨legendreMonicPolynomial_root_unit _ _ (legendreJRoot_equation p),
   legendreMonicPolynomial_root_sub_one_unit _ _ (legendreJRoot_equation p)⟩

/-- The monic presentation maps to the actual Legendre parameter ring. -/
def legendreJRootMap (p : ℕ) : LegendreJRoot p →ₐ[LegendreJBase p] LegendreBase p :=
  AdjoinRoot.liftAlgHom (legendreMonicPolynomial (legendreJScaled p))
    (Algebra.ofId _ _) (legendreParameter p) (by
      change (legendreMonicPolynomial (legendreJScaled p)).eval₂
        (legendreJMap p) (legendreParameter p) = 0
      rw [legendreMonicPolynomial_eval₂ (legendreJMap p) (legendreJScaled p)
        (legendreParameter p)]
      have : (legendreCurve (legendreParameter p)).IsElliptic := legendreModelElliptic p
      have h := legendreMonicPolynomial_j_root (legendreParameter p)
        (legendreJMap p (legendreJScaled p)) (legendreBase_units p).1
        (legendreJMap_scaled p)
      rwa [legendreMonicPolynomial_eval] at h)

/-- The universal root determines the inverse parameter specialization. -/
def legendreJRootReturn (p : ℕ) : LegendreBase p →+* LegendreJRoot p :=
  legendreSpecialize p (AdjoinRoot.root (legendreMonicPolynomial (legendreJScaled p)))
    (by
      have h := (legendreJBase_units p).1.map
        (AdjoinRoot.of (legendreMonicPolynomial (legendreJScaled p)))
      simpa only [map_ofNat] using h)
    (by
      have h := (legendreJBase_units p).2.map
        (AdjoinRoot.of (legendreMonicPolynomial (legendreJScaled p)))
      simpa only [map_natCast] using h)
    (legendreJRoot_units p).1 (legendreJRoot_units p).2

/-- The inverse specialization sends the parameter to the universal root. -/
theorem legendreJRootReturn_parameter (p : ℕ) :
    legendreJRootReturn p (legendreParameter p) =
      AdjoinRoot.root (legendreMonicPolynomial (legendreJScaled p)) :=
  legendreSpecialize_parameter p _ _ _ _ _

/-- The two maps compose to the identity on the Legendre chart. -/
theorem legendreJRootMap_retract (p : ℕ) :
    (legendreJRootMap p).toRingHom.comp (legendreJRootReturn p) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (legendreDenominator p))
  apply Polynomial.ringHom_ext'
  · exact Subsingleton.elim _ _
  · change legendreJRootMap p (legendreJRootReturn p (legendreParameter p)) =
      legendreParameter p
    rw [legendreJRootReturn_parameter]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The inverse specialization preserves the j-coordinate. -/
theorem legendreJRootReturn_j (p : ℕ) :
    legendreJRootReturn p (legendreModel p).j =
      AdjoinRoot.of (legendreMonicPolynomial (legendreJScaled p)) (X : LegendreJBase p) := by
  have : (legendreCurve (legendreParameter p)).IsElliptic := legendreModelElliptic p
  change legendreJRootReturn p (legendreCurve (legendreParameter p)).j = _
  have hj := congrArg (legendreJRootReturn p)
    (legendreCurve_j_equation (legendreParameter p) (legendreBase_units p).1)
  simp only [map_mul, map_ofNat, map_pow, map_sub, map_add, map_one,
    legendreJRootReturn_parameter] at hj
  have hr := legendreJRoot_equation p
  rw [legendreMonicPolynomial_eval] at hr
  have hk := congrArg (AdjoinRoot.of (legendreMonicPolynomial (legendreJScaled p)))
    (legendreJScaled_spec p)
  simp only [map_mul, map_ofNat] at hk
  apply (((legendreJRoot_units p).1.pow 2).mul ((legendreJRoot_units p).2.pow 2)).mul_right_cancel
  linear_combination -hj + 256 * hr +
    (AdjoinRoot.root (legendreMonicPolynomial (legendreJScaled p)) ^ 2 *
      (AdjoinRoot.root (legendreMonicPolynomial (legendreJScaled p)) - 1) ^ 2) * hk

/-- The inverse specialization is a map over the j-line. -/
theorem legendreJRootReturn_comp_jMap (p : ℕ) :
    (legendreJRootReturn p).comp (legendreJMap p) =
      AdjoinRoot.of (legendreMonicPolynomial (legendreJScaled p)) := by
  apply Polynomial.ringHom_ext'
  · apply IsLocalization.ringHom_ext (Submonoid.powers (2 * (p : ℤ)))
    exact Subsingleton.elim _ _
  · simpa only [RingHom.comp_apply, legendreJMap, coe_eval₂RingHom, eval₂_X] using
      legendreJRootReturn_j p

/-- The inverse parameter specialization as an algebra homomorphism. -/
def legendreJRootReturnAlgHom (p : ℕ) :
    LegendreBase p →ₐ[LegendreJBase p] LegendreJRoot p where
  __ := legendreJRootReturn p
  commutes' r := DFunLike.congr_fun (legendreJRootReturn_comp_jMap p) r

/-- The integral Legendre chart is the monic root algebra over the j-line. -/
def legendreJPresentation (p : ℕ) : LegendreJRoot p ≃ₐ[LegendreJBase p] LegendreBase p :=
  AlgEquiv.ofAlgHom (legendreJRootMap p) (legendreJRootReturnAlgHom p)
    (by
      apply AlgHom.ext
      intro x
      exact DFunLike.congr_fun (legendreJRootMap_retract p) x)
    (by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply, AlgHom.id_apply, legendreJRootMap,
        AdjoinRoot.liftAlgHom_root]
      exact legendreJRootReturn_parameter p)

/-- The monic presentation surjects onto the Legendre chart. -/
theorem legendreJRootMap_surjective (p : ℕ) : Function.Surjective (legendreJRootMap p) := by
  intro x
  exact ⟨legendreJRootReturn p x, DFunLike.congr_fun (legendreJRootMap_retract p) x⟩

instance legendreBaseFiniteOverJ (p : ℕ) :
    Module.Finite (LegendreJBase p) (LegendreBase p) := by
  have := (legendreMonicPolynomial_monic (legendreJScaled p)).finite_adjoinRoot
  exact Module.Finite.of_surjective (legendreJRootMap p).toLinearMap
    (legendreJRootMap_surjective p)

/-- The powers of the Legendre parameter form a basis over the j-line. -/
def legendreJBasis (p : ℕ) :
    Module.Basis (Fin (legendreMonicPolynomial (legendreJScaled p)).natDegree)
      (LegendreJBase p) (LegendreBase p) :=
  (AdjoinRoot.powerBasis' (legendreMonicPolynomial_monic (legendreJScaled p))).basis.map
    (legendreJPresentation p).toLinearEquiv

instance legendreBaseFreeOverJ (p : ℕ) :
    Module.Free (LegendreJBase p) (LegendreBase p) :=
  Module.Free.of_basis (legendreJBasis p)

/-- The monic relation has degree six at nonzero level. -/
theorem legendreJPolynomial_natDegree (p : ℕ) [NeZero p] :
    (legendreMonicPolynomial (legendreJScaled p)).natDegree = 6 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · unfold legendreMonicPolynomial
    compute_degree
  · simp only [legendreMonicPolynomial, coeff_add, coeff_sub, coeff_C_mul_X_pow]
    norm_num [coeff_C_mul, coeff_one]

/-- The Legendre chart has rank six over the j-line. -/
theorem legendreBase_finrank (p : ℕ) [NeZero p] :
    Module.finrank (LegendreJBase p) (LegendreBase p) = 6 := by
  have : Nontrivial (LegendreJBase p) := inferInstance
  have : OrzechProperty (LegendreJBase p) := CommRing.orzechProperty (LegendreJBase p)
  have : StrongRankCondition (LegendreJBase p) := inferInstance
  rw [Module.finrank_eq_card_basis (legendreJBasis p), Fintype.card_fin,
    legendreJPolynomial_natDegree]

/-- The actual scheme morphism from the Legendre chart to the j-line. -/
def legendreToJ (p : ℕ) : Spec (.of (LegendreBase p)) ⟶ Spec (.of (LegendreJBase p)) :=
  Spec.map (CommRingCat.ofHom (legendreJMap p))

instance legendreToJFinite (p : ℕ) : IsFinite (legendreToJ p) := by
  rw [legendreToJ, IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr (legendreBaseFiniteOverJ p)

instance legendreToJFlat (p : ℕ) : Flat (legendreToJ p) := by
  rw [legendreToJ, HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The cyclic parameter scheme mapped to the j-line. -/
def legendreCyclicToJ (p : ℕ) [NeZero p] :
    (legendreCyclicParameters p).left ⟶ Spec (.of (LegendreJBase p)) :=
  (legendreCyclicParameters p).hom ≫ legendreToJ p

/-- The cyclic parameter map to the j-line is finite. -/
theorem legendreCyclicToJ_finite (p : ℕ) [NeZero p] : IsFinite (legendreCyclicToJ p) := by
  have := legendreCyclicParameters_finite p
  dsimp only [legendreCyclicToJ]
  infer_instance

/-- At prime level the cyclic parameter map to the j-line is flat. -/
theorem legendreCyclicToJ_flat (p : ℕ) [Fact p.Prime] [NeZero p] :
    Flat (legendreCyclicToJ p) := by
  have := legendreCyclicParameters_etale p
  dsimp only [legendreCyclicToJ]
  infer_instance

instance legendreToJSurjective (p : ℕ) [NeZero p] : Surjective (legendreToJ p) := by
  constructor
  change Function.Surjective (PrimeSpectrum.comap (algebraMap (LegendreJBase p) (LegendreBase p)))
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := LegendreJBase p) (B := LegendreBase p)

/-- Every Legendre coefficient point has a prime cyclic parameter. -/
theorem legendreCyclicParameters_surjective (p : ℕ) [Fact p.Prime] [NeZero p] :
    Surjective (legendreCyclicParameters p).hom := by
  constructor
  intro x
  obtain ⟨y, hy⟩ := (nonzeroTorsionModel_surjective (legendreModel p) p
    (legendreBase_units p).2.1 (Fact.out : p.Prime).one_lt).1 x
  refine ⟨(scalarQuotientMap (legendreModel p) p).left y, ?_⟩
  change ((scalarQuotientMap (legendreModel p) p).left ≫
    (legendreCyclicParameters p).hom) y = x
  rw [(scalarQuotientMap (legendreModel p) p).w]
  exact hy

/-- The prime cyclic parameter scheme covers every point of the j-line. -/
theorem legendreCyclicToJ_surjective (p : ℕ) [Fact p.Prime] [NeZero p] :
    Surjective (legendreCyclicToJ p) := by
  have := legendreCyclicParameters_surjective p
  dsimp only [legendreCyclicToJ]
  infer_instance

end WeierstrassCurve.CubicCharts
