/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicEvenParameterSource
public import FLT.Mazur.CyclicCharacteristicEvenRelabeledAuxiliary

/-!
# Common relabeling retains sections on every actual even chart test

The original source comparison identifies the relabeled atlas with the same
actual normalized pullback. This comparison preserves the prescribed auxiliary
permutation and every cyclic generator power, beyond equality of moduli classes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicCharacteristicAtlas
open UniversalWeierstrass GeneralizedEllipticCurve
open GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme} (v : T ⟶ normalizedLocus n false)
  (e : RelabelGroup n)
local notation "l" => v ≫ cyclicHomNormalizedLocusInclusion n
local notation "f" => l ≫ cyclicHomUniversalMultiplicationLocusInclusion n
local notation "hf" => cyclicHomMultiplicationEquation_zero_comp n
  (cyclicHomUniversalMultiplicationLocusInclusion n) l (cyclicHomUniversalLocus_equation_zero n)
local notation "fR" => f ≫
  Over.Hom.left (cyclicHomRelabel n (Prod.fst e) (Prod.snd (Prod.snd e)))
local notation "hR" => cyclicHomRelabel_equation n (Prod.fst e)
  (Prod.snd (Prod.snd e)) f hf
local notation "qR" => cyclicHomNormalizedLocusPoint n fR hR
local notation "H" => cyclicHomSubgroup n f hf
local notation "hH" => cyclicHomSubgroup_ideal n f hf

/-- The actual common action retains the independent auxiliary labels and generator powers. -/
theorem evenNormalizedRelabel_sections :
    ∃ a : CompatibleIso
      ((normalizedSubgroup n false).baseChange (v ≫ (normalizedRelabelAction n false e).hom))
      ((normalizedSubgroup n false).baseChange v),
      (∀ i, pullSection (v ≫ (normalizedRelabelAction n false e).hom)
        (evenNormalizedAuxiliaryMarking n i) ≫ a.curve.hom.group =
          pullSection v (evenNormalizedAuxiliaryMarking n (e.1.symm i))) ∧
      ∀ m : ℕ, (pullSection (v ≫ (normalizedRelabelAction n false e).hom)
        (evenNormalizedGenerator n) ^ m) ≫ a.subgroup.hom =
          pullSection v (evenNormalizedGenerator n) ^
            (e.2.2.symm (.ofAdd (m : ZMod n))).toAdd.val := by
  have hq : v ≫ (normalizedRelabelAction n false e).hom = qR :=
    (congrArg (fun z ↦ z ≫ (normalizedRelabelAction n false e).hom)
      (evenNormalizedParameter_point n v).symm).trans
        (evenNormalizedPoint_relabel n e f hf)
  rw [hq]
  let b := evenRelabeledNormalizedSourceIso n e f hf
  let c := evenNormalizedParameterSourceIso n v
  refine ⟨b.trans c.symm, ?_, ?_⟩
  · intro i
    exact CompatibleIso.group_section_trans b c.symm _ _ _
      (evenRelabeledNormalizedSourceIso_auxiliary n e f hf i)
      (CompatibleIso.group_section_symm c _ _
        (evenNormalizedParameterSourceIso_auxiliary n v (e.1.symm i)))
  · intro m
    change _ ≫ (b.subgroup.hom ≫ c.subgroup.inv) = _
    rw [← Category.assoc, evenRelabeledNormalizedSourceIso_generator_pow]
    let j := e.2.2.symm (.ofAdd (m : ZMod n))
    have hp : (pullSection v (evenNormalizedGenerator n) ^ j.toAdd.val) ≫ c.subgroup.hom =
        (H).orbitMarking (cyclicHomSourceMarking n f) (hH) j := by
      rw [pow_comp, evenNormalizedParameterSourceIso_generator, orbitGenerator_pow]
      simp only [ZMod.natCast_zmod_val, ofAdd_toAdd]
    rw [← hp, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.CyclicCharacteristicAtlas
