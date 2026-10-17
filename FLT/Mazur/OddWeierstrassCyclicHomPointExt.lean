/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationParameter

/-!
# Odd cyclic parameters are determined by auxiliary points and all cyclic values

Auxiliary points and all cyclic values determine a complete parameter on
every test scheme, including repeated cyclic values.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}

/-- Auxiliary coordinates and all cyclic values determine the actual full parameter. -/
theorem cyclicHomPoint_ext (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (ha : f ≫ (cyclicHomAuxiliary n).left = g ≫ (cyclicHomAuxiliary n).left)
    (hc : ∀ c, f ≫ (cyclicHomParameter n ≫ value universalGroup _ c).left =
      g ≫ (cyclicHomParameter n ≫ value universalGroup _ c).left) : f = g := by
  have hb : f ≫ (cyclicHomAuxiliaryScheme n).hom =
      g ≫ (cyclicHomAuxiliaryScheme n).hom := by
    simpa only [Category.assoc, (cyclicHomAuxiliary n).w] using
      congrArg (fun h ↦ h ≫ levelThree.hom) ha
  let p : Over.mk (f ≫ (cyclicHomAuxiliaryScheme n).hom) ⟶ cyclicHomAuxiliaryScheme n :=
    Over.homMk f rfl
  let q : Over.mk (f ≫ (cyclicHomAuxiliaryScheme n).hom) ⟶ cyclicHomAuxiliaryScheme n :=
    Over.homMk g hb.symm
  have he : p = q := by
    apply cyclicHom_hom_ext
    · exact Over.OverMorphism.ext ha
    · apply homScheme_ext
      intro c
      apply Over.OverMorphism.ext
      exact (Category.assoc _ _ _).trans ((hc c).trans (Category.assoc _ _ _).symm)
  exact congrArg Over.Hom.left he

end FLT.Mazur.OddWeierstrassParameter
