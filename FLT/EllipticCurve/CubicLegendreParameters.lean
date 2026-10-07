/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendre
public import FLT.EllipticCurve.CubicUniversalCyclicGroup

/-! # Integral Legendre parameters with cyclic subgroups

The localization of ℤ[λ] at 2pλ(λ-1) represents Legendre parameters
with invertible level. Its elliptic equation carries the actual finite
étale prime cyclic parameter scheme.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts

/-- The product inverted on the integral Legendre chart of level p. -/
def legendreDenominator (p : ℕ) : ℤ[X] := 2 * (p : ℤ[X]) * X * (X - 1)

/-- The integral Legendre parameter ring. -/
abbrev LegendreBase (p : ℕ) := Localization.Away (legendreDenominator p)

instance legendreBaseDomain (p : ℕ) [NeZero p] : IsDomain (LegendreBase p) :=
  Localization.Away.isDomain (by
    dsimp [legendreDenominator]
    apply mul_ne_zero
    · exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast NeZero.ne p)) X_ne_zero
    · simpa using X_sub_C_ne_zero (1 : ℤ))

/-- The universal Legendre parameter. -/
def legendreParameter (p : ℕ) : LegendreBase p :=
  algebraMap ℤ[X] (LegendreBase p) X

/-- The elliptic equation over the Legendre parameter ring. -/
def legendreModel (p : ℕ) : WeierstrassCurve (LegendreBase p) :=
  legendreCurve (legendreParameter p)

/-- The four factors defining the chart are units. -/
theorem legendreBase_units (p : ℕ) :
    IsUnit (2 : LegendreBase p) ∧ IsUnit (p : LegendreBase p) ∧
      IsUnit (legendreParameter p) ∧ IsUnit (legendreParameter p - 1) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := LegendreBase p) (legendreDenominator p)
  simpa only [legendreDenominator, map_mul, map_ofNat, map_natCast, map_sub,
    map_one, legendreParameter, IsUnit.mul_iff, and_assoc] using h

instance legendreModelElliptic (p : ℕ) : (legendreModel p).IsElliptic :=
  legendreCurve_elliptic _ (legendreBase_units p).1
    (legendreBase_units p).2.2.1 (legendreBase_units p).2.2.2

instance legendreBaseLevelUnit (p : ℕ) : Fact (IsUnit (p : LegendreBase p)) :=
  ⟨(legendreBase_units p).2.1⟩

/-- Specialization at a nonsingular Legendre parameter with invertible level. -/
def legendreSpecialize {S : Type*} [CommRing S] (p : ℕ) (l : S)
    (h2 : IsUnit (2 : S)) (hp : IsUnit (p : S))
    (h0 : IsUnit l) (h1 : IsUnit (l - 1)) : LegendreBase p →+* S :=
  IsLocalization.Away.lift (legendreDenominator p)
    (show IsUnit ((eval₂RingHom (Int.castRingHom S) l) (legendreDenominator p)) by
      simpa [legendreDenominator] using ((h2.mul hp).mul h0).mul h1)

/-- Specialization recovers the given Legendre parameter. -/
theorem legendreSpecialize_parameter {S : Type*} [CommRing S] (p : ℕ) (l : S)
    (h2 : IsUnit (2 : S)) (hp : IsUnit (p : S))
    (h0 : IsUnit l) (h1 : IsUnit (l - 1)) :
    legendreSpecialize p l h2 hp h0 h1 (legendreParameter p) = l := by
  change ((legendreSpecialize p l h2 hp h0 h1).comp
    (algebraMap ℤ[X] (LegendreBase p))) X = l
  rw [legendreSpecialize, IsLocalization.Away.lift_comp]
  simp

/-- Specialization recovers the Legendre equation. -/
theorem legendreModel_specialize {S : Type*} [CommRing S] (p : ℕ) (l : S)
    (h2 : IsUnit (2 : S)) (hp : IsUnit (p : S))
    (h0 : IsUnit l) (h1 : IsUnit (l - 1)) :
    (legendreModel p).map (legendreSpecialize p l h2 hp h0 h1) = legendreCurve l := by
  ext <;> simp [legendreModel, legendreCurve, WeierstrassCurve.map,
    legendreSpecialize_parameter]

/-- Every map from the parameter ring is its canonical specialization. -/
theorem legendreSpecialize_parameterMap {S : Type*} [CommRing S] (p : ℕ)
    (f : LegendreBase p →+* S) :
    legendreSpecialize p (f (legendreParameter p))
      (by simpa only [map_ofNat] using (legendreBase_units p).1.map f)
      (by simpa using (legendreBase_units p).2.1.map f)
      ((legendreBase_units p).2.2.1.map f)
      (by simpa using (legendreBase_units p).2.2.2.map f) = f := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (legendreDenominator p))
  rw [legendreSpecialize, IsLocalization.Away.lift_comp]
  apply Polynomial.ringHom_ext'
  · exact Subsingleton.elim _ _
  · simp [legendreParameter]

/-- The Legendre ring represents parameters with the four required units. -/
def legendreParameterEquiv (p : ℕ) (S : Type*) [CommRing S] :
    (LegendreBase p →+* S) ≃
      {l : S // IsUnit (2 : S) ∧ IsUnit (p : S) ∧ IsUnit l ∧ IsUnit (l - 1)} where
  toFun f := ⟨f (legendreParameter p),
    ⟨by simpa only [map_ofNat] using (legendreBase_units p).1.map f,
     by simpa using (legendreBase_units p).2.1.map f,
     (legendreBase_units p).2.2.1.map f,
     by simpa using (legendreBase_units p).2.2.2.map f⟩⟩
  invFun l := legendreSpecialize p l.val l.property.1 l.property.2.1
    l.property.2.2.1 l.property.2.2.2
  left_inv f := legendreSpecialize_parameterMap p f
  right_inv l := Subtype.ext (legendreSpecialize_parameter p l.val l.property.1
    l.property.2.1 l.property.2.2.1 l.property.2.2.2)

/-- The actual cyclic parameter scheme over the integral Legendre chart. -/
abbrev legendreCyclicParameters (p : ℕ) [NeZero p] :
    Over (Spec (.of (LegendreBase p))) :=
  scalarQuotientModel (legendreModel p) p

/-- Cyclic parameters are finite over the Legendre chart. -/
theorem legendreCyclicParameters_finite (p : ℕ) [NeZero p] :
    IsFinite (legendreCyclicParameters p).hom :=
  scalarQuotientModel_finite (legendreModel p) p

/-- Prime cyclic parameters are étale over the Legendre chart. -/
theorem legendreCyclicParameters_etale (p : ℕ) [Fact p.Prime] [NeZero p] :
    Etale (legendreCyclicParameters p).hom :=
  scalarQuotientModel_etale (legendreModel p) p

/-- Geometric fibers classify the order-p subgroups
of the specialized Legendre equation. -/
def legendreCyclicFieldPointEquiv (p : ℕ) [Fact p.Prime] [NeZero p]
    (K : Type) [Field K] [IsAlgClosed K] [DecidableEq K]
    (l : K) (h2 : IsUnit (2 : K)) (hp : IsUnit (p : K))
    (h0 : IsUnit l) (h1 : IsUnit (l - 1)) :
    (letI : Algebra (LegendreBase p) K := (legendreSpecialize p l h2 hp h0 h1).toAlgebra;
      pointSource (R := LegendreBase p) K ⟶ legendreCyclicParameters p) ≃
      {H : AddSubgroup (legendreCurve l).toAffine.Point // Nat.card H = p} := by
  letI : Algebra (LegendreBase p) K := (legendreSpecialize p l h2 hp h0 h1).toAlgebra
  let e := scalarQuotientPrimeSubgroupEquiv (legendreModel p) p K
  exact e.trans (Equiv.cast (congrArg
    (fun C : WeierstrassCurve K => {H : AddSubgroup C.toAffine.Point // Nat.card H = p})
    (legendreModel_specialize p l h2 hp h0 h1)))

end WeierstrassCurve.CubicCharts
