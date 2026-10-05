/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLiftedOverlapCoefficients

/-!
# Balance of normalized first-coordinate lifts

The first-coordinate sections agree when the extra scalars are supplied
through the first pair or the outer pair of the triple overlap.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineDirectTripleBalance
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

/-- The two first-coordinate lifts agree for both extra scalars. -/
theorem firstLift_balance (n : coefficients S M) (s t : S) :
    coord3 R S t • mappedUnit (CommRingCat.ofHom (pair12 R S).toRingHom) _
      (comparison (left R S) (pair12 R S).toRingHom
        (coord1 R S) (pair12_left R S) M).hom (firstSections R S M (n ⊗ₜ[R] s)) =
      coord2 R S s • mappedUnit (CommRingCat.ofHom (pair13 R S).toRingHom) _
        (comparison (left R S) (pair13 R S).toRingHom
          (coord1 R S) (pair13_left R S) M).hom (firstSections R S M (n ⊗ₜ[R] t)) := by
  rw [first_normalized, first_normalized, smul_smul, smul_smul]
  apply congrArg (· • specUnit (CommRingCat.ofHom (coord1 R S)) M n)
  change ((1 : S) ⊗ₜ[R] ((1 : S) ⊗ₜ[R] t)) *
    ((1 : S) ⊗ₜ[R] (s ⊗ₜ[R] (1 : S))) =
      ((1 : S) ⊗ₜ[R] (s ⊗ₜ[R] (1 : S))) *
        ((1 : S) ⊗ₜ[R] ((1 : S) ⊗ₜ[R] t))
  exact mul_comm _ _

end FLT.Mazur.AffineDirectTripleBalance
