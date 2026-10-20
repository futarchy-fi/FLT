/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterStages

/-!
# A unique original character homomorphism at the next adic order

The adjacent quotient map has its full square-zero kernel. Applying the
surjective lifting construction produces a homomorphism at the next order
whose reduction is exactly the given original homomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart AdicFormallySmoothStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type} [CommRing R] [AddCommGroup G] (I : Ideal R) (t : R)
  (ht : t ∈ I) (m : ℕ) (g : stageSource I G m ⟶ stageGroup I t m)

/-- The constructed homomorphism at the next original positive adic order. -/
def step : stageSource I G (m + 1) ⟶ stageGroup I t (m + 1) := by
  letI := (restriction I m).toRingHom.toAlgebra
  exact nilpotentSurjectiveHomLift (parameter I t (m + 1))
    (parameter_nilpotent I t ht (m + 1)) (restriction_surjective I m)
    (restriction_kernel_square I m)
    (g ≫ eqToHom (congrArg integralSmoothGroup (restriction_equation I t m).symm))

/-- The entire next-order homomorphism reduces to the original previous-order map. -/
theorem step_reduction :
    Spec.map (CommRingCat.ofHom (characterRestriction I G m)) ≫
      (step I t ht m g).hom.hom.hom.left =
        g.hom.hom.hom.left ≫ smoothRestriction I t m := by
  let _ := (restriction I m).toRingHom.toAlgebra
  have h := nilpotentSurjectiveHomLift_reduction (parameter I t (m + 1))
      (parameter_nilpotent I t ht (m + 1)) (restriction_surjective I m)
      (restriction_kernel_square I m)
      (g ≫ eqToHom (congrArg integralSmoothGroup (restriction_equation I t m).symm))
  change Spec.map (CommRingCat.ofHom (characterRestriction I G m)) ≫
    (step I t ht m g).hom.hom.hom.left =
      (g.hom.hom.hom.left ≫ _) ≫ _ at h
  exact h.trans (Category.assoc _ _ _)

/-- Any homomorphism with the same original reduction is this constructed next-order map. -/
theorem step_unique (q : stageSource I G (m + 1) ⟶ stageGroup I t (m + 1))
    (hq : Spec.map (CommRingCat.ofHom (characterRestriction I G m)) ≫
      q.hom.hom.hom.left = g.hom.hom.hom.left ≫ smoothRestriction I t m) :
    q = step I t ht m g := by
  let _ := (restriction I m).toRingHom.toAlgebra
  apply nilpotentSurjectiveHomLift_unique (parameter I t (m + 1))
    (parameter_nilpotent I t ht (m + 1)) (restriction_surjective I m)
    (restriction_kernel_square I m)
    (g ≫ eqToHom (congrArg integralSmoothGroup (restriction_equation I t m).symm)) q
  change Spec.map (CommRingCat.ofHom (characterRestriction I G m)) ≫
    q.hom.hom.hom.left = (g.hom.hom.hom.left ≫ _) ≫ _
  exact hq.trans (Category.assoc _ _ _).symm

end FLT.Mazur.OneGonAdicCharacterTower
