/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicPresentationScalarTowers
public import FLT.Mazur.AdicFormalPresentationHom

/-!
# Projecting algebraic formal differentials onto completed original spaces

The continuous original derivation defines a comparison FROM the algebraic
cotangent space of the completed presentation TO the completed original
space. No equality or equivalence of these different modules is asserted.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicOriginalSpaceProjection

open AdicExtensionProjection AdicFormalPresentationHom
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (P : Algebra.Extension R A) (I : Ideal A)

/-- The completed presentation uses the actual projection as its algebra map. -/
local instance completedAlgebra :
    Algebra (AdicCompletion (ideal P I) P.Ring) (AdicCompletion I A) :=
  (AdicExtensionProjection.projection P I).toAlgebra

attribute [local instance] AdicPresentationDerivation.spaceModule

/-- The continuous original differential factors through algebraic formal differentials. -/
def projection : (completed P I).CotangentSpace →ₗ[AdicCompletion I A]
    AdicCompletion I P.CotangentSpace := by
  let _ := AdicPresentationScalarTowers.relativeTower P I
  let _ : IsScalarTower (AdicCompletion (ideal P I) P.Ring) (AdicCompletion I A)
      (AdicCompletion I P.CotangentSpace) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact (AdicPresentationDerivation.derivation P I).liftKaehlerDifferential.liftBaseChange _

/-- The comparison evaluates an algebraic formal tensor by the continuous original derivative. -/
theorem projection_tmul (a : AdicCompletion I A) (x : (completed P I).Ring) :
    projection P I (a ⊗ₜ[(completed P I).Ring]
      KaehlerDifferential.D R (completed P I).Ring x) =
        a • AdicPresentationDerivation.derivation P I x := by
  let _ := AdicPresentationScalarTowers.relativeTower P I
  let _ : IsScalarTower (AdicCompletion (ideal P I) P.Ring) (AdicCompletion I A)
      (AdicCompletion I P.CotangentSpace) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  change (AdicPresentationDerivation.derivation P I).liftKaehlerDifferential.liftBaseChange _
    (a ⊗ₜ[AdicCompletion (ideal P I) P.Ring]
      KaehlerDifferential.D R (AdicCompletion (ideal P I) P.Ring) x) = _
  rw [LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D]

/-- On a completed relation, the projected conormal differential is its continuous derivative. -/
theorem projection_cotangentComplex_mk (x : (completed P I).ker) :
    projection P I ((completed P I).cotangentComplex (Algebra.Extension.Cotangent.mk x)) =
      AdicPresentationDerivation.derivation P I x.val := by
  rw [Algebra.Extension.cotangentComplex_mk, projection_tmul, one_smul]

end FLT.Mazur.AdicOriginalSpaceProjection
