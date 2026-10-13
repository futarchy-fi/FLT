/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomNormalizationParameter
public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeFixedGroup

/-!
# Actual cyclic homomorphism normalization fixes the closed auxiliary frame

Auxiliary coordinates and all cyclic values determine a complete parameter.
The identity normalization comparison fixes every cyclic value, including
coincident values, over an already normalized frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
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
      congrArg (fun h ↦ h ≫ levelFour.hom) ha
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

/-- Normalization fixes all labels whenever the auxiliary frame is already normalized. -/
theorem cyclicHomNormalizedPoint_fixed (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (hn : SatisfiesNormalization (cyclicHomAuxiliaryPoint n f).appTop.hom) :
    cyclicHomNormalizedPoint n f = f := by
  apply cyclicHomPoint_ext n
  · rw [cyclicHomNormalizedPoint_auxiliary, auxiliarySchemeNormalizedPoint_fixed _ hn]
    rfl
  · intro c
    rw [cyclicHomNormalizedPoint_value,
      auxiliarySchemeNormalizationGroupIso_fixed_inv_fst (cyclicHomAuxiliaryPoint n f) hn]
    exact cyclicHomSourceMarking_fst n f c

/-- Repeated normalization fixes the entire original cyclic homomorphism parameter. -/
theorem cyclicHomNormalizedPoint_idempotent (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) :
    cyclicHomNormalizedPoint n (cyclicHomNormalizedPoint n f) = cyclicHomNormalizedPoint n f := by
  apply cyclicHomNormalizedPoint_fixed
  change SatisfiesNormalization
    (cyclicHomNormalizedPoint n f ≫ (cyclicHomAuxiliary n).left).appTop.hom
  rw [cyclicHomNormalizedPoint_auxiliary]
  exact auxiliarySchemeNormalizedPoint_satisfies _

end FLT.Mazur.UniversalWeierstrass
