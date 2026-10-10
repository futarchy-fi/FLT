/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberNormalForm

/-!
# The actual conic component at middle depth

The residual conic has equation v*(v+a)=c*t². Its coordinate algebra and
universal property retain c, the original incidence ratio and tangent slope.
The full horizontal fiber maps onto this conic and its incidence line.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassModificationX

variable {R : Type*} [CommRing R] (a c : R)

/-- The middle-depth conic polynomial over the incidence-coordinate line. -/
def conicPolynomial : R[X][X] := X * (X + C (C a)) - C (C c * X ^ 2)

/-- The coordinate algebra of the full residual conic. -/
abbrev ConicCoordinate := AdjoinRoot (conicPolynomial a c)

/-- The conic keeps the original incidence coordinate. -/
def conicT : ConicCoordinate a c := algebraMap R[X] _ X

/-- The conic keeps the original tangent slope. -/
def conicV : ConicCoordinate a c := AdjoinRoot.root (conicPolynomial a c)

/-- Evaluating the conic polynomial preserves the nonzero middle-depth coefficient. -/
theorem conicPolynomial_eval {S : Type*} [CommRing S] (f : R[X] →+* S) (w : S) :
    (conicPolynomial a c).eval₂ f w =
      w * (w + f (C a)) - f (C c) * f X ^ 2 := by
  simp only [conicPolynomial, eval₂_sub, eval₂_mul, eval₂_add, eval₂_X, eval₂_C,
    map_mul, map_pow, eval₂_pow]

/-- The conic satisfies exactly its original residual equation. -/
theorem conic_relation : conicV a c * (conicV a c + algebraMap R _ a) -
    algebraMap R _ c * conicT a c ^ 2 = 0 := by
  have h := AdjoinRoot.eval₂_root (conicPolynomial a c)
  rw [conicPolynomial_eval] at h
  have hc (r : R) : algebraMap R[X] (ConicCoordinate a c) (C r) =
      algebraMap R _ r := (IsScalarTower.algebraMap_apply R R[X] _ r).symm
  simpa only [AdjoinRoot.algebraMap_eq, ← hc, conicT, conicV] using h

/-- Every solution of the conic equation gives the actual algebra map. -/
def conicEvaluation {S : Type*} [CommRing S] [Algebra R S] (u w : S)
    (h : w * (w + algebraMap R S a) - algebraMap R S c * u ^ 2 = 0) :
    ConicCoordinate a c →ₐ[R] S :=
  AdjoinRoot.liftAlgHom (conicPolynomial a c) (aeval u) w (by
    rw [conicPolynomial_eval]
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, aeval_X] using h)

/-- Evaluation preserves the original conic incidence coordinate. -/
@[simp] theorem conicEvaluation_t {S : Type*} [CommRing S] [Algebra R S] (u w : S)
    (h : w * (w + algebraMap R S a) - algebraMap R S c * u ^ 2 = 0) :
    conicEvaluation a c u w h (conicT a c) = u := by
  simp [conicEvaluation, conicT, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of]

/-- Evaluation preserves the original conic slope. -/
@[simp] theorem conicEvaluation_v {S : Type*} [CommRing S] [Algebra R S] (u w : S)
    (h : w * (w + algebraMap R S a) - algebraMap R S c * u ^ 2 = 0) :
    conicEvaluation a c u w h (conicV a c) = w := AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The two original coordinates determine maps out of the conic. -/
theorem conic_hom_ext {S : Type*} [CommRing S] [Algebra R S]
    (f g : ConicCoordinate a c →ₐ[R] S)
    (ht : f (conicT a c) = g (conicT a c))
    (hv : f (conicV a c) = g (conicV a c)) : f = g := by
  apply AdjoinRoot.algHom_ext'
  · exact Polynomial.algHom_ext ht
  · exact hv

/-- The original x coordinate in the full horizontal fiber. -/
def fiberConicFactor : FiberCoordinate a c :=
  fiberV a c * (fiberV a c + algebraMap R _ a) - algebraMap R _ c * fiberT a c ^ 2

/-- The full horizontal fiber maps onto its residual conic. -/
def fiberConicMap : FiberCoordinate a c →ₐ[R] ConicCoordinate a c :=
  fiberEvaluation a c (conicT a c) (conicV a c) (by rw [conic_relation, mul_zero])

/-- The conic map retains the incidence function. -/
@[simp] theorem fiberConicMap_t : fiberConicMap a c (fiberT a c) = conicT a c :=
  fiberEvaluation_t _ _ _ _ _

/-- The conic map retains the slope function. -/
@[simp] theorem fiberConicMap_v : fiberConicMap a c (fiberV a c) = conicV a c :=
  fiberEvaluation_v _ _ _ _ _

/-- The original conic factor vanishes under the conic map. -/
@[simp] theorem fiberConicMap_factor : fiberConicMap a c (fiberConicFactor a c) = 0 := by
  simpa only [fiberConicFactor, map_sub, map_mul, map_add, map_pow, AlgHom.commutes,
    fiberConicMap_t, fiberConicMap_v] using conic_relation a c

/-- The incidence line remains present with the entire middle-depth coefficient retained. -/
def fiberIncidenceMap : FiberCoordinate a c →ₐ[R] R[X] :=
  fiberEvaluation a c 0 X (by simp)

/-- The incidence line sets t to zero. -/
@[simp] theorem fiberIncidenceMap_t : fiberIncidenceMap a c (fiberT a c) = 0 :=
  fiberEvaluation_t _ _ _ _ _

/-- The incidence line keeps v as its free polynomial coordinate. -/
@[simp] theorem fiberIncidenceMap_v : fiberIncidenceMap a c (fiberV a c) = X :=
  fiberEvaluation_v _ _ _ _ _

/-- The intersection with the conic retains both oriented roots on the incidence line. -/
@[simp] theorem fiberIncidenceMap_factor :
    fiberIncidenceMap a c (fiberConicFactor a c) = X * (X + C a) := by
  simp only [fiberConicFactor, map_sub, map_mul, map_add, map_pow, AlgHom.commutes,
    fiberIncidenceMap_t, fiberIncidenceMap_v, algebraMap_eq, zero_pow (by decide : 2 ≠ 0),
    mul_zero, sub_zero]

end FLT.Mazur.WeierstrassModificationX
