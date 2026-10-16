/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartCoefficientMap

/-!
# Normalized cubic charts under arbitrary coefficient homomorphisms

The chart coefficient map can be used without installing a permanent algebra
instance. It preserves every original normalized coordinate and scalar.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
variable {R S : Type*} [CommRing R] [CommRing S]
  (f : R →+* S) (W : WeierstrassCurve R) (j : Fin 3)

/-- The full normalized original chart under an arbitrary coefficient ring homomorphism. -/
def chartCoefficientRingMap : Coordinate W j →+* Coordinate (W.map f) j := by
  let _ := f.toAlgebra
  exact (chartCoefficientMap (S := S) W j).toRingHom

/-- All normalized projective coordinates are unchanged by the coefficient ring map. -/
theorem chartCoefficientRingMap_coord (i : Fin 3) :
    chartCoefficientRingMap f W j (coord W j i) = coord (W.map f) j i := by
  let _ := f.toAlgebra
  exact chartCoefficientMap_coord W j i

/-- The complete coefficient ring map retains the actual base ring homomorphism. -/
theorem chartCoefficientRingMap_scalar (a : R) :
    chartCoefficientRingMap f W j (algebraMap R _ a) = algebraMap S _ (f a) := by
  let _ := f.toAlgebra
  exact (chartCoefficientMap (S := S) W j).commutes a

/-- Transport to an independently specified target curve keeps every original coefficient. -/
def chartCoefficientRingMapTo (U : WeierstrassCurve S) (hW : W.map f = U) :
    Coordinate W j →+* Coordinate U j := by
  subst U
  exact chartCoefficientRingMap f W j

/-- The transported comparison retains every original normalized coordinate. -/
theorem chartCoefficientRingMapTo_coord (U : WeierstrassCurve S) (hW : W.map f = U)
    (i : Fin 3) :
    chartCoefficientRingMapTo f W j U hW (coord W j i) = coord U j i := by
  subst U
  exact chartCoefficientRingMap_coord f W j i

/-- Transport of the curve preserves the actual arithmetic scalar map. -/
theorem chartCoefficientRingMapTo_scalar (U : WeierstrassCurve S) (hW : W.map f = U)
    (a : R) :
    chartCoefficientRingMapTo f W j U hW (algebraMap R _ a) = algebraMap S _ (f a) := by
  subst U
  exact chartCoefficientRingMap_scalar f W j a

end FLT.Mazur.WeierstrassIntegralChart
