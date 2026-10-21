/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelBaseChangeFaithfulness

/-!
# The faithful marking open commutes with arbitrary base change

Restrict the actual equation-scheme comparison using universal faithfulness.
The inverse is constructed from the same represented marking, so this is an
isomorphism of schemes over the new base, including on nonreduced tests.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (E : Over S) [GrpObj E]
  (A : Type) [Group A] [Fintype A]

/-- Universal faithfulness can be tested before the pullback adjunction. -/
theorem homSchemeBaseChange_faithful_iff {U : Over T}
    (q : U ⟶ (Over.pullback g).obj (homScheme E A)) :
    UniversallyFaithful ((Over.pullback g).obj E) A
      (q ≫ (homSchemeBaseChangeIso g E A).hom) ↔
    UniversallyFaithful E A (((Over.mapPullbackAdj g).homEquiv U _).symm q) := by
  have h := changeBasePoint_universallyFaithful_iff g E A
    (((Over.mapPullbackAdj g).homEquiv U _).symm q)
  rwa [changeBasePoint_eq, Equiv.apply_symm_apply] at h

variable [IsSeparated E.hom]

local instance pullbackGroup_separated : IsSeparated ((Over.pullback g).obj E).hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.hom g))

/-- The original faithful open gives faithful markings over the new base. -/
theorem faithfulBaseChange_marking :
    UniversallyFaithful ((Over.pullback g).obj E) A
      ((Over.pullback g).map (faithfulInclusion E A) ≫
        (homSchemeBaseChangeIso g E A).hom) := by
  apply (homSchemeBaseChange_faithful_iff g E A _).mpr
  have h := (Over.mapPullbackAdj g).homEquiv_naturality_right_symm
    (𝟙 ((Over.pullback g).obj (faithfulScheme E A))) (faithfulInclusion E A)
  rw [Category.id_comp] at h
  rw [h]
  exact faithfulInclusion_universallyFaithful E A _

/-- Restriction of the original marking comparison to the faithful opens. -/
def faithfulBaseChangeHom :
    (Over.pullback g).obj (faithfulScheme E A) ⟶
      faithfulScheme ((Over.pullback g).obj E) A :=
  faithfulLift _ A _ (faithfulBaseChange_marking g E A)

/-- The restricted comparison retains the entire original marking parameter. -/
@[reassoc] theorem faithfulBaseChangeHom_inclusion :
    faithfulBaseChangeHom g E A ≫ faithfulInclusion ((Over.pullback g).obj E) A =
      (Over.pullback g).map (faithfulInclusion E A) ≫
        (homSchemeBaseChangeIso g E A).hom :=
  faithfulLift_inclusion _ A _ _

/-- The inverse parameter is faithful on every test over the original base. -/
theorem faithfulBaseChange_inverse_marking :
    UniversallyFaithful E A
      (((Over.mapPullbackAdj g).homEquiv _ _).symm
        (faithfulInclusion ((Over.pullback g).obj E) A ≫
          (homSchemeBaseChangeIso g E A).inv)) := by
  apply (homSchemeBaseChange_faithful_iff g E A _).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [Category.id_comp] using
    faithfulInclusion_universallyFaithful ((Over.pullback g).obj E) A (𝟙 _)

/-- The inverse faithful comparison, obtained from the full original test marking. -/
def faithfulBaseChangeInv :
    faithfulScheme ((Over.pullback g).obj E) A ⟶
      (Over.pullback g).obj (faithfulScheme E A) :=
  (Over.mapPullbackAdj g).homEquiv _ _
    (faithfulLift E A _ (faithfulBaseChange_inverse_marking g E A))

/-- The inverse retains the actual equation-scheme comparison as well. -/
@[reassoc] theorem faithfulBaseChangeInv_inclusion :
    faithfulBaseChangeInv g E A ≫ (Over.pullback g).map (faithfulInclusion E A) =
      faithfulInclusion ((Over.pullback g).obj E) A ≫
        (homSchemeBaseChangeIso g E A).inv := by
  rw [faithfulBaseChangeInv, ← Adjunction.homEquiv_naturality_right,
    faithfulLift_inclusion, Equiv.apply_symm_apply]

/-- Faithful marking schemes commute with arbitrary, possibly nonflat base change. -/
def faithfulBaseChangeIso :
    (Over.pullback g).obj (faithfulScheme E A) ≅
      faithfulScheme ((Over.pullback g).obj E) A where
  hom := faithfulBaseChangeHom g E A
  inv := faithfulBaseChangeInv g E A
  hom_inv_id := by
    let _ : Mono (faithfulInclusion E A) :=
      by
        have : Mono (faithfulInclusion E A).left :=
          inferInstanceAs (Mono (faithfulOpen E A).ι)
        exact Over.mono_of_mono_left (faithfulInclusion E A)
    apply (cancel_mono ((Over.pullback g).map (faithfulInclusion E A))).mp
    rw [Category.assoc, faithfulBaseChangeInv_inclusion,
      faithfulBaseChangeHom_inclusion_assoc, Iso.hom_inv_id, Category.comp_id,
      Category.id_comp]
  inv_hom_id := by
    let _ : Mono (faithfulInclusion ((Over.pullback g).obj E) A) :=
      by
        have : Mono (faithfulInclusion ((Over.pullback g).obj E) A).left :=
          inferInstanceAs (Mono (faithfulOpen ((Over.pullback g).obj E) A).ι)
        exact Over.mono_of_mono_left (faithfulInclusion ((Over.pullback g).obj E) A)
    apply (cancel_mono (faithfulInclusion ((Over.pullback g).obj E) A)).mp
    rw [Category.assoc, faithfulBaseChangeHom_inclusion,
      faithfulBaseChangeInv_inclusion_assoc, Iso.inv_hom_id, Category.comp_id,
      Category.id_comp]

end FLT.Mazur.AuxiliaryLevel
