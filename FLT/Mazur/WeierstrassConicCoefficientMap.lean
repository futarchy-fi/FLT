/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberConic

/-!
# Actual coefficient maps between the complete residual conics

Both incidence and slope coordinates are preserved by arbitrary coefficient
homomorphisms. The constant in the middle-depth equation is retained.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T)
  (a c : S) (b d : T) (ha : f a = b) (hc : f c = d)

/-- Extend the original incidence polynomial coefficients into the specialized conic. -/
def conicCoefficientBase : S[X] →+* ConicCoordinate b d :=
  Polynomial.eval₂RingHom ((algebraMap T _).comp f) (conicT b d)

include ha hc in
/-- The original conic equation vanishes at the specialized incidence and slope. -/
theorem conicCoefficientBase_relation :
    (conicPolynomial a c).eval₂ (conicCoefficientBase f b d) (conicV b d) = 0 := by
  rw [conicPolynomial_eval]
  simpa only [conicCoefficientBase, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_C, Polynomial.eval₂_X, RingHom.comp_apply, ha, hc] using conic_relation b d

/-- The full conic coefficient map, without any reducedness or nonzero-constant hypothesis. -/
def conicCoefficientMap : ConicCoordinate a c →+* ConicCoordinate b d :=
  AdjoinRoot.lift (conicCoefficientBase f b d) (conicV b d)
    (conicCoefficientBase_relation f a c b d ha hc)

/-- Every original coefficient specializes through the prescribed ring homomorphism. -/
theorem conicCoefficientMap_scalar (s : S) :
    conicCoefficientMap f a c b d ha hc (algebraMap S _ s) = algebraMap T _ (f s) := by
  change conicCoefficientMap f a c b d ha hc
    (AdjoinRoot.of (conicPolynomial a c) (C s)) = _
  rw [conicCoefficientMap, AdjoinRoot.lift_of]
  exact Polynomial.eval₂_C _ _

/-- The entire conic incidence coordinate is unchanged by coefficient specialization. -/
@[simp] theorem conicCoefficientMap_t :
    conicCoefficientMap f a c b d ha hc (conicT a c) = conicT b d := by
  change conicCoefficientMap f a c b d ha hc
    (AdjoinRoot.of (conicPolynomial a c) X) = _
  rw [conicCoefficientMap, AdjoinRoot.lift_of]
  exact Polynomial.eval₂_X _ _

/-- The signed conic slope specializes as the original coordinate. -/
@[simp] theorem conicCoefficientMap_v :
    conicCoefficientMap f a c b d ha hc (conicV a c) = conicV b d :=
  AdjoinRoot.lift_root _

section Algebra
variable {R : Type*} [CommRing R] [Algebra R S] [Algebra R T]
  (g : S →ₐ[R] T) (ga : g a = b) (gc : g c = d)

/-- The full conic specialization also preserves the original integral coefficient ring. -/
def conicCoefficientAlgHom : ConicCoordinate a c →ₐ[R] ConicCoordinate b d where
  __ := conicCoefficientMap g.toRingHom a c b d ga gc
  commutes' r := by
    change conicCoefficientMap g.toRingHom a c b d ga gc (algebraMap R _ r) = _
    rw [IsScalarTower.algebraMap_apply R S, conicCoefficientMap_scalar]
    change algebraMap T _ (g (algebraMap R S r)) = _
    rw [g.commutes, ← IsScalarTower.algebraMap_apply R T]

end Algebra
end FLT.Mazur.WeierstrassModificationX
