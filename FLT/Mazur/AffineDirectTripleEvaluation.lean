/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineDirectTripleSections
public import FLT.Mazur.AffineLiftedOverlapCoefficients
public import FLT.Mazur.AffineTensorCocycle

/-!
# Triple-coordinate formulas for normalized pair transports

The direct third-coordinate chart evaluates the two ways of inserting an
extra scalar. These identities compare actual pair pullback units and
supply the coefficient calculations used by the geometric cocycle.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineDirectTripleEvaluation
open AffineOverlapTensor AffineOverlapPullback AffineTripleOverlapMaps
open AffineTripleOverlapPullback AffineDirectTripleSections AffineTensorCocycle
open AffineIteratedPullbackSections AffineLiftedOverlapCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
/-- Coefficient scalars restricted to the base ring. -/
local instance : Module R (coefficients S M) := Module.compHom _ (algebraMap R S)
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- The outer scalar multiplies the normalized last-pair pullback. -/
theorem directSections_outer_tmul (s t : S) (n : coefficients S M) :
  directSections R S M (s ⊗ₜ[R] (t ⊗ₜ[R] n)) =
    (s ⊗ₜ[R] (1 : S ⊗[R] S)) •
      mappedUnit (CommRingCat.ofHom (pair23 R S).toRingHom) _
        (comparison (right R S) (pair23 R S).toRingHom
          (coord3 R S) (pair23_right R S) M).hom (secondSections R S M (t ⊗ₜ[R] n)) := by
  have h := second_normalized R S M (pair23 R S).toRingHom
    (coord3 R S) (pair23_right R S) n t
  rw [h, directSections_tmul, smul_smul]
  apply congrArg (· • specUnit (CommRingCat.ofHom (coord3 R S)) M n)
  change s ⊗ₜ[R] (t ⊗ₜ[R] (1 : S)) =
    (s ⊗ₜ[R] ((1 : S) ⊗ₜ[R] (1 : S))) *
      ((1 : S) ⊗ₜ[R] (t ⊗ₜ[R] (1 : S)))
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Inserting a middle scalar is the normalized outer-pair pullback. -/
theorem directSections_insertMiddle_tmul (s a : S) (n : coefficients S M) :
  directSections R S M (insertMiddle s (a ⊗ₜ[R] n)) =
    coord2 R S s •
      mappedUnit (CommRingCat.ofHom (pair13 R S).toRingHom) _
        (comparison (right R S) (pair13 R S).toRingHom
          (coord3 R S) (pair13_right R S) M).hom (secondSections R S M (a ⊗ₜ[R] n)) := by
  change directSections R S M (a ⊗ₜ[R] (s ⊗ₜ[R] n)) = _
  have h := second_normalized R S M (pair13 R S).toRingHom
    (coord3 R S) (pair13_right R S) n a
  rw [directSections_tmul, h, smul_smul]
  apply congrArg (· • specUnit (CommRingCat.ofHom (coord3 R S)) M n)
  change a ⊗ₜ[R] (s ⊗ₜ[R] (1 : S)) =
    ((1 : S) ⊗ₜ[R] (s ⊗ₜ[R] (1 : S))) *
      (a ⊗ₜ[R] ((1 : S) ⊗ₜ[R] (1 : S)))
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

end FLT.Mazur.AffineDirectTripleEvaluation
