/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryTorsionSections

/-!
# Distinct auxiliary labels have disjoint torsion images

A point in the intersection would give a nonempty pullback test on which two
marked sections agree. Universal faithfulness then identifies their labels.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.OddWeierstrassParameter

open IntegralWeierstrassParameter (OddChartRing)
open UniversalWeierstrass (Labels labels_pow)

/-- Distinct label sections have disjoint images in the full torsion scheme. -/
theorem auxiliaryTorsionSection_disjoint :
    Pairwise fun a b : Labels 3 ↦
      Disjoint (Set.range (auxiliaryTorsionSection a))
        (Set.range (auxiliaryTorsionSection b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  let sa := auxiliaryTorsionSection a
  let sb := auxiliaryTorsionSection b
  let p := pullback.fst sa sb
  let q := pullback.snd sa sb
  have hpq : p = q := by
    have h := congrArg (fun k ↦ k ≫ auxiliaryThreeTorsionMap)
      (pullback.condition (f := sa) (g := sb))
    simpa only [sa, sb, Category.assoc, auxiliaryTorsionSection_map, Category.comp_id] using h
  let U : Over parameterBase := Over.mk (p ≫ levelThree.hom)
  let f : U ⟶ levelThree := Over.homMk p rfl
  obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
  let _ : Nonempty U.left := ⟨z⟩
  have ht : f ≫ auxiliaryTorsionMarking a = f ≫ auxiliaryTorsionMarking b := by
    apply Over.OverMorphism.ext
    have h := congrArg (fun k ↦ k ≫ pullback.fst threeTorsion.hom levelThree.hom)
      (pullback.condition (f := sa) (g := sb))
    have ht : p ≫ (auxiliaryTorsionMarking a).left =
        q ≫ (auxiliaryTorsionMarking b).left := by
      simpa only [sa, sb, Category.assoc, auxiliaryTorsionSection_fst] using h
    change p ≫ (auxiliaryTorsionMarking a).left = p ≫ (auxiliaryTorsionMarking b).left
    rw [hpq] at ht ⊢
    exact ht
  have hm : f ≫ levelThreeMarking a = f ≫ levelThreeMarking b := by
    simpa only [Category.assoc, auxiliaryTorsionMarking_inclusion] using
      congrArg (fun k ↦ k ≫ GroupTorsionScheme.inclusion universalGroup 3) ht
  apply hab
  apply levelThreeMarking_injective f
  simpa only [AuxiliaryLevel.markingOf_comp, levelThreeMarking] using hm

end FLT.Mazur.OddWeierstrassParameter
