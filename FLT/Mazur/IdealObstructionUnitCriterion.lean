/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealObstructionScalarExtension
public import FLT.Mazur.LocalIdealTensorCriterion

/-!
# A presentation-free scalar-extension obstruction criterion

A canonical free presentation removes the presentation data from the
obstruction-vanishing criterion. The original module can be arbitrary;
only its quotient-coefficient extension is required to be flat.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealObstructionUnitCriterion
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (S : Type*) [CommRing S] [Algebra R S] (I : Ideal R)
  [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)]

/-- Vanishing of the actual obstruction transition suffices, without a chosen presentation. -/
theorem ideal_injective
    (h : ∀ z : (I.subtype.rTensor M).ker,
      TensorProduct.map (IdealTensorKernel.idealTransition (algebraMap R S) I)
        (ScalarExtensionUnit.unit S M) z.val = 0) :
    Function.Injective ((I.map (algebraMap R S)).subtype.rTensor (S ⊗[R] M)) := by
  generalize hqdef : LocalIdealTensorCriterion.presentation (R := R) M = q
  have hq : Function.Surjective q := by
    rw [← hqdef]
    exact LocalIdealTensorCriterion.presentation_surjective M
  apply IdealObstructionScalarExtension.ideal_injective
    (R := R) (P := q.ker) (N := M →₀ R) S I q.ker.subtype q
    (LinearMap.exact_subtype_ker_map q) hq
  exact h

end FLT.Mazur.IdealObstructionUnitCriterion
