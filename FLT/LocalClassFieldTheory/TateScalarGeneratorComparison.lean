/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateNegativeCocycleClass

/-!
# Scalar bar generators and the canonical abelianization comparison

The canonical comparison sends the bar generator at `g` to `g`, and these
bar classes exhaust integral Tate degree minus two.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupHomology

variable (G : Type) [Group G] [Fintype G]

local notation "T" => Rep.trivial ℤ G ℤ

/-- The scalar generator maps to the usual single-chain homology class. -/
theorem tateScalarGenerator_homology (g : G) :
    ((TateCohomology.isoGroupHomology (-2) 1 (by decide)).app T).hom
      (tateScalarGenerator ℤ G g) =
        H1π T ((cycles₁IsoOfIsTrivial T).inv (Finsupp.single g (1 : ℤ))) := by
  rw [tateScalarGenerator, tateCocycleClass_negative_two T _
    (tateScalarGenerator_cycle ℤ G g)]
  change π T 1 _ = π T 1 ((isoCycles₁ T).inv _)
  apply congrArg (π T 1)
  apply (ModuleCat.mono_iff_injective (iCycles T 1)).mp inferInstance
  rw [isoCycles₁_inv_comp_iCycles_apply]
  exact (inhomogeneousChains T).i_cyclesMk _ _ _ _

/-- The canonical scalar abelianization comparison preserves the group generator. -/
theorem tateScalarAbelianizationEquiv_generator (g : G) :
    tateScalarAbelianizationEquiv G (tateScalarGenerator ℤ G g) =
      Additive.ofMul (Abelianization.of g) := by
  change TensorProduct.rid ℤ (Additive (Abelianization G))
    (H1AddEquivOfIsTrivial T
      (((TateCohomology.isoGroupHomology (-2) 1 (by decide)).app T).hom
        (tateScalarGenerator ℤ G g))) = _
  rw [tateScalarGenerator_homology, H1AddEquivOfIsTrivial_single]
  simp

/-- Every integral scalar Tate class is represented by one group element. -/
theorem tateScalarGenerator_surjective : Function.Surjective (tateScalarGenerator ℤ G) := by
  intro x
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective
    (Additive.toMul (tateScalarAbelianizationEquiv G x))
  change Abelianization.of g = Additive.toMul (tateScalarAbelianizationEquiv G x) at hg
  refine ⟨g, (tateScalarAbelianizationEquiv G).injective ?_⟩
  rw [tateScalarAbelianizationEquiv_generator, hg]
  rfl

end LocalClassFieldTheory
