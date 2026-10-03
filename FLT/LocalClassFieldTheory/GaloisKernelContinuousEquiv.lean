/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.GaloisKernelRestriction

/-!
# A continuous identification of the restriction kernel

The known continuous inverse is a map from a compact Galois group to a
Hausdorff subgroup. Compactness supplies continuity in the other direction.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable (K C : Type) [Field K] [Field C] [Algebra K C] [IsGalois K C]
  (E : IntermediateField K C) [IsGalois K E]

/-- The algebraic identification of the restriction kernel is continuous in both directions. -/
theorem galoisRestrictionKernelEquiv_continuous :
    Continuous (galoisRestrictionKernelEquiv K C E) :=
  (galoisRestrictionKernelEquiv_symm_continuous K C E).continuous_symm_of_equiv_compact_to_t2

omit [IsGalois K C] in
/-- The kernel identification preserves the underlying automorphism of the overfield. -/
theorem galoisRestrictionKernelEquiv_apply
    (g : (AlgEquiv.restrictNormalHom E : Gal(C/K) →* Gal(E/K)).ker) (x : C) :
    galoisRestrictionKernelEquiv K C E g x = g.val x := rfl

end LocalClassFieldTheory
