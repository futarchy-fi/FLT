/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryFaithfulLift

/-!
# The finite relabeling action on the faithful boundary open

Universal distinctness survives the prescribed permutation of cyclic labels.
The lifted action retains the entire original parameter, including auxiliary labels.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
open CyclicCharacteristicAtlas (RelabelGroup)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [GrpObj E] (n : ℕ) [NeZero n]

/-- Relabeling preserves universal distinctness over arbitrary scheme tests. -/
theorem cyclicSectionMarking_action_distinct {T : Scheme} (g : T ⟶ S)
    (f : Over.mk g ⟶ parameter E n)
    (hf : UniversallyDistinctSections.UniversallyDistinct
      (fun i : ZMod n ↦ cyclicSectionMarking E n g f (.ofAdd i)))
    (e : RelabelGroup n) :
    UniversallyDistinctSections.UniversallyDistinct
      (fun i : ZMod n ↦ cyclicSectionMarking E n g (f ≫ (action E n e).hom) (.ofAdd i)) := by
  intro V k hV i j hij
  apply Multiplicative.ofAdd.injective
  apply e.2.2.symm.injective
  have h := hf V k hV (a₁ := (e.2.2.symm (.ofAdd i)).toAdd)
    (a₂ := (e.2.2.symm (.ofAdd j)).toAdd)
  exact congrArg Multiplicative.ofAdd (h (by
    simpa only [cyclicSectionMarking_action, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, ofAdd_toAdd] using hij))

variable [IsSeparated E.hom]

/-- Morphisms to the faithful open are determined by their original parameters. -/
theorem cyclicFaithfulInclusion_ext {T : Over S}
    {f g : T ⟶ cyclicFaithfulParameter E n}
    (h : f ≫ cyclicFaithfulInclusion E n = g ≫ cyclicFaithfulInclusion E n) : f = g := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (cyclicFaithfulOpen E n).ι).mp
  exact congrArg Over.Hom.left h

/-- Lift the actual finite relabeling to the constructed faithful open. -/
def faithfulRelabel (e : RelabelGroup n) :
    cyclicFaithfulParameter E n ⟶ cyclicFaithfulParameter E n :=
  cyclicFaithfulLift E n (cyclicFaithfulParameter E n).hom
    (cyclicFaithfulInclusion E n ≫ (action E n e).hom)
    (cyclicSectionMarking_action_distinct E n _ _
      (by
        have hh := cyclicFaithfulSection_distinct E n
          (cyclicFaithfulParameter E n).hom (𝟙 (cyclicFaithfulParameter E n))
        have he : (𝟙 (cyclicFaithfulParameter E n)) ≫ cyclicFaithfulInclusion E n =
            cyclicFaithfulInclusion E n := Category.id_comp _
        rw [he] at hh
        exact hh) e)

/-- The lifted relabeling retains the full original parameter action. -/
@[reassoc] theorem faithfulRelabel_inclusion (e : RelabelGroup n) :
    faithfulRelabel E n e ≫ cyclicFaithfulInclusion E n =
      cyclicFaithfulInclusion E n ≫ (action E n e).hom :=
  cyclicFaithfulLift_inclusion E n _ _ _

/-- The identity relabeling is the identity on the actual open. -/
@[simp] theorem faithfulRelabel_one : faithfulRelabel E n 1 = 𝟙 _ := by
  apply cyclicFaithfulInclusion_ext E n
  rw [faithfulRelabel_inclusion, map_one, Category.id_comp]
  exact Category.comp_id _

/-- The lifted maps obey the same left-action convention as the ambient scheme. -/
theorem faithfulRelabel_mul (e f : RelabelGroup n) :
    faithfulRelabel E n (e * f) = faithfulRelabel E n f ≫ faithfulRelabel E n e := by
  apply cyclicFaithfulInclusion_ext E n
  rw [faithfulRelabel_inclusion, Category.assoc, faithfulRelabel_inclusion,
    faithfulRelabel_inclusion_assoc, map_mul]
  rfl

/-- The common finite group acts by automorphisms on the actual faithful open. -/
def faithfulAction : RelabelGroup n →* Aut (cyclicFaithfulParameter E n) where
  toFun e :=
    { hom := faithfulRelabel E n e
      inv := faithfulRelabel E n e⁻¹
      hom_inv_id := by rw [← faithfulRelabel_mul, inv_mul_cancel, faithfulRelabel_one]
      inv_hom_id := by rw [← faithfulRelabel_mul, mul_inv_cancel, faithfulRelabel_one] }
  map_one' := by apply Aut.ext; exact faithfulRelabel_one E n
  map_mul' e f := by apply Aut.ext; exact faithfulRelabel_mul E n e f

/-- Forgetting the base gives the original finite scheme action restricted to the open. -/
def faithfulSchemeAction : RelabelGroup n →* Aut (cyclicFaithfulParameter E n).left :=
  (Functor.mapAut _ (Over.forget S)).comp (faithfulAction E n)

end FLT.Mazur.CyclicBoundaryParameter
