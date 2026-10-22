/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealObstructionOrientation
public import FLT.Mazur.IdealResidualFlatBaseChange
public import FLT.Mazur.LocalProperIdealTensorCriterion

/-!
# Local flatness after killing the old ideal obstruction

For a scalar-extended module finite over a local Noetherian target, residual
flatness and vanishing of the old-to-new obstruction imply flatness over
the new local Noetherian base. The extended ideal need only be proper.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.LocalScalarObstructionCriterion
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (S T : Type*) [CommRing S] [Algebra R S] [IsNoetherianRing S] [IsLocalRing S]
  [CommRing T] [Algebra S T] [IsNoetherianRing T] [IsLocalRing T]
  [IsLocalHom (algebraMap S T)]
  [Module T (S ⊗[R] M)] [IsScalarTower S T (S ⊗[R] M)] [Module.Finite T (S ⊗[R] M)]

include T in
/-- The old obstruction vanishing criterion proves flatness of the entire extended module. -/
theorem flat (I : Ideal R) (hI : I.map (algebraMap R S) ≠ ⊤)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)]
    (h : ∀ z : (ModuleIdealTensor.inclusion (S := R) (M := M) I).ker,
      TensorProduct.map (ScalarExtensionUnit.unit S M)
        (IdealTensorKernel.idealTransition (algebraMap R S) I) z.val = 0) :
    Module.Flat S (S ⊗[R] M) := by
  let _ := IdealResidualFlatBaseChange.flat (M := M) S I
  apply LocalProperIdealTensorCriterion.flat_of_ideal_injective
    (S := T) (I.map (algebraMap R S)) hI
  exact IdealObstructionOrientation.inclusion_injective (S := R) S I h

end FLT.Mazur.LocalScalarObstructionCriterion
