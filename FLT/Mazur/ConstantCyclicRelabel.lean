/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstantCyclicSectionMap

/-!
# Relabeling automorphisms of the constant cyclic group scheme

Permute the actual coproduct components by a cyclic group automorphism.
The resulting scheme isomorphism preserves multiplication and every section label.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.ConstantCyclicRelabel
set_option backward.isDefEq.respectTransparency false
universe u
variable (S : Scheme.{u}) (n : ℕ) [NeZero n]

/-- All component sections bundled as their actual cyclic group homomorphism. -/
def componentMarking : Multiplicative (ZMod n) →*
    (𝟙_ (Over S) ⟶ ConstantCyclicGroup.model S n) where
  toFun i := ConstantCyclicGroup.component S n i.toAdd
  map_one' := ConstantCyclicGenerator.component_zero S n
  map_mul' i j := ConstantCyclicGenerator.component_add S n i.toAdd j.toAdd

/-- The scheme map that applies the given permutation to every cyclic component. -/
def relabel (e : MulAut (Multiplicative (ZMod n))) :
    ConstantCyclicGroup.model S n ⟶ ConstantCyclicGroup.model S n :=
  ConstantCyclicSectionMap.toScheme ((componentMarking S n).comp e.toMonoidHom)

/-- Relabeling preserves the actual group-scheme operations. -/
instance relabel_isMonHom (e : MulAut (Multiplicative (ZMod n))) :
    IsMonHom (relabel S n e) := ConstantCyclicSectionMap.toScheme_isMonHom _

/-- Each component moves by exactly the prescribed automorphism. -/
@[reassoc] theorem component_relabel (e : MulAut (Multiplicative (ZMod n))) (i : ZMod n) :
    ConstantCyclicGroup.component S n i ≫ relabel S n e =
      ConstantCyclicGroup.component S n (e (.ofAdd i)).toAdd :=
  ConstantCyclicSectionMap.component_toScheme _ i

/-- The permutation of components is an actual isomorphism over the base. -/
def relabelIso (e : MulAut (Multiplicative (ZMod n))) :
    ConstantCyclicGroup.model S n ≅ ConstantCyclicGroup.model S n where
  hom := relabel S n e
  inv := relabel S n e.symm
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    change ConstantCyclicGroup.component S n i ≫ _ = _
    rw [component_relabel_assoc, component_relabel, ofAdd_toAdd,
      e.symm_apply_apply, toAdd_ofAdd, Category.comp_id]
  inv_hom_id := by
    apply Sigma.hom_ext
    intro i
    change ConstantCyclicGroup.component S n i ≫ _ = _
    rw [component_relabel_assoc, component_relabel, ofAdd_toAdd,
      e.apply_symm_apply, toAdd_ofAdd, Category.comp_id]

/-- Relabeling a marking is precomposition by the actual group-scheme isomorphism. -/
@[reassoc] theorem relabel_toScheme {G : Over S} [GrpObj G]
    (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ G))
    (e : MulAut (Multiplicative (ZMod n))) :
    relabel S n e ≫ ConstantCyclicSectionMap.toScheme φ =
      ConstantCyclicSectionMap.toScheme (φ.comp e.toMonoidHom) := by
  apply Sigma.hom_ext
  intro i
  change ConstantCyclicGroup.component S n i ≫ _ = _
  rw [component_relabel_assoc, ConstantCyclicSectionMap.component_toScheme,
    ConstantCyclicSectionMap.component_toScheme, ofAdd_toAdd]
  rfl

end FLT.Mazur.ConstantCyclicRelabel
