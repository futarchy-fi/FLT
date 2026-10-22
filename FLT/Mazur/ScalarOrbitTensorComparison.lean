/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupFreeOrbitComparison

/-!
# Orbit comparison over the original scalar ring

The original scalar ring may map into a proper subring of the full fixed ring.
Freeness still constructs a surjective orbit comparison. Its kernel is exactly
the kernel of changing the tensor base to the fixed ring; it is not discarded.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarOrbitTensorComparison
open FiniteGroupQuotient
variable (G R A : Type*) [Group G] [CommRing R] [CommRing A]
  [MulSemiringAction G A] [Algebra R A] [Algebra R (invariantRing G A)]
  [IsScalarTower R (invariantRing G A) A]
local notation "S" => invariantRing G A

/-- Change only the tensor base, retaining both original source factors. -/
def toFixedTensor : A ⊗[R] A →ₐ[R] A ⊗[S] A :=
  Algebra.TensorProduct.mapOfCompatibleSMul S R R A A

/-- The original scalar comparison is defined before any scalar fullness is known. -/
def comparison : A ⊗[R] A →ₐ[R] (G → A) :=
  ((orbitTensorComparison G A).restrictScalars R).comp (toFixedTensor G R A)

/-- Its coordinates are the actual two endpoint evaluations. -/
@[simp] theorem comparison_tmul (a b : A) (g : G) :
    comparison G R A (a ⊗ₜ[R] b) g = a * (g • b) := rfl

/-- Every fixed-base tensor has a preimage over the unchanged scalar ring. -/
theorem toFixedTensor_surjective : Function.Surjective (toFixedTensor G R A) :=
  Algebra.TensorProduct.mapOfCompatibleSMul_surjective S R R A A

variable [Finite G] (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤)
include hfree

/-- Freeness constructs a closed orbit relation even without original scalar fullness. -/
theorem comparison_surjective : Function.Surjective (comparison G R A) :=
  (orbitTensorComparison_surjective G A hfree).comp (toFixedTensor_surjective G R A)

/-- The original comparison loses precisely the extra fixed-ring balancing equations. -/
theorem comparison_ker : RingHom.ker (comparison G R A).toRingHom =
    RingHom.ker (toFixedTensor G R A).toRingHom := by
  apply RingHom.ker_comp_of_injective
  exact (freeOrbitTensorEquiv G A hfree).injective

/-- Equality of all orbit coordinates detects equality after exactly this change of base. -/
theorem comparison_eq_iff (x y : A ⊗[R] A) :
    comparison G R A x = comparison G R A y ↔
      toFixedTensor G R A x = toFixedTensor G R A y :=
  (freeOrbitTensorEquiv G A hfree).injective.eq_iff

end FLT.Mazur.ScalarOrbitTensorComparison
