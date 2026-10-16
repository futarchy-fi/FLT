/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOpenCoefficientMap

/-!
# Explicit target transport on the full initial node neighborhood

The coefficient map lands in an independently named curve and smoothing.
Both original node coordinates and every scalar survive this transport.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s : R) (U : WeierstrassCurve S) (s' : S)
  (hW : W.map f = U) (hs : f s = s')

/-- Coefficient change on the full node open with explicit target data. -/
def nodeOpenCoefficientRingMapTo : PolynomialNodeOpen W s →+* PolynomialNodeOpen U s' := by
  subst U s'
  exact nodeOpenCoefficientRingMap f W s

/-- Explicit transport preserves every scalar of the full neighborhood. -/
@[simp] theorem nodeOpenCoefficientRingMapTo_scalar (a : R) :
    nodeOpenCoefficientRingMapTo f W s U s' hW hs (algebraMap R _ a) =
      algebraMap S _ (f a) := by
  subst U s'
  exact nodeOpenCoefficientRingMap_scalar f W s a

/-- The first node coordinate is preserved on the full neighborhood. -/
@[simp] theorem nodeOpenCoefficientRingMapTo_p :
    nodeOpenCoefficientRingMapTo f W s U s' hW hs
      (algebraMap (NodalFiber.Coordinate s) _ (NodalFiber.p s)) =
        algebraMap (NodalFiber.Coordinate s') _ (NodalFiber.p s') := by
  subst U s'
  exact nodeOpenCoefficientRingMap_p f W s

/-- The opposite node coordinate is preserved on the full neighborhood. -/
@[simp] theorem nodeOpenCoefficientRingMapTo_q :
    nodeOpenCoefficientRingMapTo f W s U s' hW hs
      (algebraMap (NodalFiber.Coordinate s) _ (NodalFiber.q s)) =
        algebraMap (NodalFiber.Coordinate s') _ (NodalFiber.q s') := by
  subst U s'
  exact nodeOpenCoefficientRingMap_q f W s

end FLT.Mazur.WeierstrassModificationX
