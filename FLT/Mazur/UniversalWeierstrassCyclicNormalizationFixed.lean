/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeFixedGroup
public import FLT.Mazur.UniversalWeierstrassCyclicNormalizedSlice

/-!
# Full cyclic normalization fixes every normalized frame

Coefficients and all labels determine an actual full scheme point. The proved
identity comparison of proper group families fixes every cyclic label, not
merely the auxiliary factor, on arbitrary source schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
namespace FLT.Mazur.UniversalWeierstrass
open AuxiliaryLevel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme}

/-- Full cyclic scheme maps are determined by their coefficient maps and every marked label. -/
theorem cyclicSchemePoint_ext (f g : T ⟶ (cyclicAuxiliaryScheme n).left)
    (hb : f ≫ (cyclicAuxiliaryScheme n).hom = g ≫ (cyclicAuxiliaryScheme n).hom)
    (hm : ∀ c, f ≫ (cyclicAuxiliaryInclusion n ≫ value universalGroup (CyclicLabels n) c).left =
      g ≫ (cyclicAuxiliaryInclusion n ≫ value universalGroup (CyclicLabels n) c).left) :
    f = g := by
  let p : Over.mk (f ≫ (cyclicAuxiliaryScheme n).hom) ⟶ cyclicAuxiliaryScheme n :=
    Over.homMk f rfl
  let q : Over.mk (f ≫ (cyclicAuxiliaryScheme n).hom) ⟶ cyclicAuxiliaryScheme n :=
    Over.homMk g hb.symm
  have he : p = q := by
    apply (faithfulRepresentation universalGroup (CyclicLabels n) _).injective
    apply Subtype.ext
    apply homScheme_ext
    intro c
    apply Over.OverMorphism.ext
    exact (Category.assoc _ _ _).trans ((hm c).trans (Category.assoc _ _ _).symm)
  exact congrArg Over.Hom.left he

/-- Normalization fixes the complete cyclic point whenever its actual auxiliary frame is fixed. -/
theorem cyclicSchemeNormalizedPoint_fixed (f : T ⟶ (cyclicAuxiliaryScheme n).left)
    (hn : SatisfiesNormalization (cyclicSchemeAuxiliaryPoint n f).appTop.hom) :
    cyclicSchemeNormalizedPoint n f = f := by
  apply cyclicSchemePoint_ext n
  · rw [cyclicSchemeNormalizedPoint_base,
      auxiliarySchemeNormalizedPoint_fixed (cyclicSchemeAuxiliaryPoint n f) hn]
    exact (Category.assoc _ _ _).trans (congrArg (fun z ↦ f ≫ z) (forgetCyclic n).w)
  · intro c
    rw [cyclicSchemeNormalizedPoint_value,
      auxiliarySchemeNormalizationGroupIso_fixed_inv_fst (cyclicSchemeAuxiliaryPoint n f) hn]
    exact cyclicSchemeOriginalMarking_fst n f c

end FLT.Mazur.UniversalWeierstrass
