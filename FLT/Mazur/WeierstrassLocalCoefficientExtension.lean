/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLocalGenericProjection

/-!
# Extending specified local cubic equations

A compatible homomorphism of coefficient rings transports each original
variable change to the prescribed larger generic field. This applies to both
the source cubic and the original quotient target without choosing a new target.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.WeierstrassLocalCoefficientExtension
variable {R K L A B : Type} [CommRing R] [CommRing K] [CommRing L]
  [CommRing A] [CommRing B] [Algebra R K] [Algebra R L] [Algebra K L]
  [IsScalarTower R K L] [Algebra A K] [Algebra B L]
  (φ : A →+* B)
  (hφ : (algebraMap B L).comp φ = (algebraMap K L).comp (algebraMap A K))
  (E : WeierstrassCurve R) (W : WeierstrassCurve A) (C : VariableChange K)
  (hC : C • E.map (algebraMap R K) = W.map (algebraMap A K))

include hφ in
/-- The integral coefficient extension has exactly the expected generic equation. -/
theorem genericEquation :
    (W.map φ).map (algebraMap B L) = (W.map (algebraMap A K)).map (algebraMap K L) := by
  rw [map_map, hφ, map_map]

include hφ hC in
/-- The same original coordinate change, extended to L, presents the extended integral cubic. -/
theorem changeEquation :
    C.map (algebraMap K L) • E.map (algebraMap R L) =
      (W.map φ).map (algebraMap B L) := by
  rw [genericEquation φ hφ W, IsScalarTower.algebraMap_eq R K L, ← map_map,
    map_variableChange, hC]

/-- The coefficient compatibility needed for extending valuation-ring models is pointwise. -/
theorem compatibility_of_apply
    (h : ∀ a, algebraMap B L (φ a) = algebraMap K L (algebraMap A K a)) :
    (algebraMap B L).comp φ = (algebraMap K L).comp (algebraMap A K) :=
  RingHom.ext h

end FLT.Mazur.WeierstrassLocalCoefficientExtension
