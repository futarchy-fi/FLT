/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLiftedOverlapCoefficients

/-!
# Balance of normalized middle-coordinate lifts

The second chart through pair12 agrees with the first chart through pair23
when each lift is multiplied by the omitted coordinate scalar.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineDirectTripleMiddleBalance
open AffineOverlapTensor AffineOverlapPullback AffineTripleOverlapMaps
open AffineTripleOverlapPullback
open AffineIteratedPullbackSections AffineLiftedOverlapCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
/-- The pair12 and pair23 lifts agree after multiplying by the missing scalars. -/
theorem middleLift_balance (n : coefficients S M) (a t : S) :
    coord3 R S t • mappedUnit (CommRingCat.ofHom (pair12 R S).toRingHom) _
    (comparison (right R S) (pair12 R S).toRingHom
      (coord2 R S) (pair12_right R S) M).hom (secondSections R S M (a ⊗ₜ[R] n)) =
      (a ⊗ₜ[R] (1 : S ⊗[R] S)) •
        mappedUnit (CommRingCat.ofHom (pair23 R S).toRingHom) _
          (comparison (left R S) (pair23 R S).toRingHom
            (coord2 R S) (pair23_left R S) M).hom (firstSections R S M (n ⊗ₜ[R] t)) := by
  rw [second_normalized, first_normalized, smul_smul, smul_smul]
  apply congrArg (· • specUnit (CommRingCat.ofHom (coord2 R S)) M n)
  change ((1 : S) ⊗ₜ[R] ((1 : S) ⊗ₜ[R] t)) *
    (a ⊗ₜ[R] ((1 : S) ⊗ₜ[R] (1 : S))) =
      (a ⊗ₜ[R] ((1 : S) ⊗ₜ[R] (1 : S))) *
        ((1 : S) ⊗ₜ[R] ((1 : S) ⊗ₜ[R] t))
  exact mul_comm _ _

end FLT.Mazur.AffineDirectTripleMiddleBalance
