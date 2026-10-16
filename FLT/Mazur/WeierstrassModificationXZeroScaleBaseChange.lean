/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXScaleTransport
public import FLT.Mazur.WeierstrassModificationXBaseChangeGenerators
public import FLT.Mazur.PrincipalOpenTransportGeometry

/-!
# The original tensor chart with vanishing scale and all divided coefficients

Only the scale is set to zero. The original x and y functions, all divided
coefficients, and the full y-localization survive this coefficient comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (hs : algebraMap R S s = 0)
local notation "V" => W.map (algebraMap R S)
local notation "c3" => algebraMap R S b3
local notation "c4" => algebraMap R S b4
local notation "c6" => algebraMap R S b6
local notation "T" => ScalarExtension W s b3 b4 b6 S
local notation "A" => Coordinate V 0 c3 c4 c6

/-- The complete original tensor algebra at scale zero, with no other coefficient discarded. -/
irreducible_def zeroScaleBaseChangeEquiv : T ≃ₐ[S] A :=
  (baseChangeEquiv W s b3 b4 b6 S).trans
    (initialScaleTransportEquiv V (algebraMap R S s) 0 c3 c4 c6 hs)

local notation "E" => zeroScaleBaseChangeEquiv W s b3 b4 b6 S hs

/-- The original incidence coordinate is unchanged by the scale-zero comparison. -/
theorem zeroScaleBaseChangeEquiv_t :
    E ((1 : S) ⊗ₜ[R] t W s b3 b4 b6) = t V 0 c3 c4 c6 := by
  rw [zeroScaleBaseChangeEquiv_def, AlgEquiv.trans_apply, baseChangeEquiv_t,
    initialScaleTransportEquiv_t]

/-- The original slope is unchanged by the scale-zero comparison. -/
theorem zeroScaleBaseChangeEquiv_v :
    E ((1 : S) ⊗ₜ[R] v W s b3 b4 b6) = v V 0 c3 c4 c6 := by
  rw [zeroScaleBaseChangeEquiv_def, AlgEquiv.trans_apply, baseChangeEquiv_v,
    initialScaleTransportEquiv_v]

/-- The coefficient map into the complete scale-zero chart. -/
def zeroScaleCoefficientMap : Coordinate W s b3 b4 b6 →ₐ[R] A :=
  ((E).toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight

local notation "F" => zeroScaleCoefficientMap W s b3 b4 b6 S hs

/-- The original x function survives all coefficient and scale transports. -/
theorem zeroScaleCoefficientMap_x : F (x W s b3 b4 b6) = x V 0 c3 c4 c6 := by
  have ht : F (t W s b3 b4 b6) = t V 0 c3 c4 c6 :=
    zeroScaleBaseChangeEquiv_t W s b3 b4 b6 S hs
  have hv : F (v W s b3 b4 b6) = v V 0 c3 c4 c6 :=
    zeroScaleBaseChangeEquiv_v W s b3 b4 b6 S hs
  simp only [x, map_sub, map_add, map_mul, map_pow, AlgHom.commutes, ht, hv,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, ← IsScalarTower.algebraMap_apply R S]

/-- The original y function also survives, including its original slope factor. -/
theorem zeroScaleCoefficientMap_y : F (y W s b3 b4 b6) = y V 0 c3 c4 c6 := by
  rw [y, map_mul, zeroScaleCoefficientMap_x]
  exact congrArg (x V 0 c3 c4 c6 * ·) (zeroScaleBaseChangeEquiv_v W s b3 b4 b6 S hs)

/-- The whole original tensor y-localization is the full scale-zero y-localization. -/
def zeroScaleInfinityBoundaryEquiv :
    Localization.Away ((1 : S) ⊗ₜ[R] y W s b3 b4 b6) ≃ₐ[S]
      Localization.Away (y V 0 c3 c4 c6) :=
  PrincipalOpenTransport.equiv E _ _ (zeroScaleCoefficientMap_y W s b3 b4 b6 S hs)

/-- All original tensor functions are retained on the full infinity boundary. -/
theorem zeroScaleInfinityBoundaryEquiv_base (z : ScalarExtension W s b3 b4 b6 S) :
    zeroScaleInfinityBoundaryEquiv W s b3 b4 b6 S hs
      (algebraMap (S ⊗[R] Coordinate W s b3 b4 b6)
        (Localization.Away ((1 : S) ⊗ₜ[R] y W s b3 b4 b6)) z) =
        algebraMap A (Localization.Away (y V 0 c3 c4 c6)) (E z) :=
  PrincipalOpenTransport.equiv_base _ _ _ _ z

end FLT.Mazur.WeierstrassModificationX
