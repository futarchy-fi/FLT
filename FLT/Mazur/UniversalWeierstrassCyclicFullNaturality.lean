/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryValueNaturality
public import FLT.Mazur.UniversalWeierstrassCyclicNormalizationFixed
public import FLT.Mazur.UniversalWeierstrassCyclicNormalizationMap

/-!
# Full cyclic normalization is natural on all test schemes

Every full label is normalized by the same actual family comparison. The
coefficient and label equations identify independent normalization with the
global normalization morphism, including nonaffine and nonreduced sources.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
namespace FLT.Mazur.UniversalWeierstrass
open AuxiliaryLevel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T U : Scheme} (f : T ⟶ (cyclicAuxiliaryScheme n).left)

/-- Every original cyclic value lies over the original auxiliary coefficient parameter. -/
theorem cyclicSchemeValue_base (c : CyclicLabels n) :
    (f ≫ (cyclicAuxiliaryInclusion n ≫ value universalGroup (CyclicLabels n) c).left) ≫
        universalGroup.hom = cyclicSchemeAuxiliaryPoint n f ≫ levelFour.hom := by
  rw [Category.assoc, (cyclicAuxiliaryInclusion n ≫
    value universalGroup (CyclicLabels n) c).w]
  exact ((Category.assoc _ _ _).trans
    (congrArg (fun z ↦ f ≫ z) (forgetCyclic n).w)).symm

/-- Every full label is the actual normalization of its original universal value. -/
theorem cyclicSchemeNormalizedPoint_value_normalize (c : CyclicLabels n) :
    cyclicSchemeNormalizedPoint n f ≫
        (cyclicAuxiliaryInclusion n ≫ value universalGroup (CyclicLabels n) c).left =
      auxiliarySchemeNormalizedValue (cyclicSchemeAuxiliaryPoint n f)
        (f ≫ (cyclicAuxiliaryInclusion n ≫ value universalGroup (CyclicLabels n) c).left)
        (cyclicSchemeValue_base n f c) := by
  have hl : pullback.lift
      (f ≫ (cyclicAuxiliaryInclusion n ≫ value universalGroup (CyclicLabels n) c).left)
      (𝟙 T) ((cyclicSchemeValue_base n f c).trans (Category.id_comp _).symm) =
    (cyclicSchemeOriginalMarking n f c).left := by
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans (cyclicSchemeOriginalMarking_fst n f c).symm
    · exact (pullback.lift_snd _ _ _).trans (cyclicSchemeOriginalMarking n f c).w.symm
  rw [cyclicSchemeNormalizedPoint_value, auxiliarySchemeNormalizedValue, hl]
  rfl

/-- Independent normalization of every full cyclic point commutes with arbitrary source maps. -/
theorem cyclicSchemeNormalizedPoint_natural (k : U ⟶ T) :
    cyclicSchemeNormalizedPoint n (k ≫ f) = k ≫ cyclicSchemeNormalizedPoint n f := by
  apply cyclicSchemePoint_ext n
  · rw [cyclicSchemeNormalizedPoint_base, Category.assoc, cyclicSchemeNormalizedPoint_base]
    have ha : cyclicSchemeAuxiliaryPoint n (k ≫ f) =
        k ≫ cyclicSchemeAuxiliaryPoint n f := Category.assoc _ _ _
    rw [ha, auxiliarySchemeNormalizedPoint_natural_base, Category.assoc]
  · intro c
    rw [Category.assoc, cyclicSchemeNormalizedPoint_value_normalize,
      cyclicSchemeNormalizedPoint_value_normalize]
    exact auxiliarySchemeNormalizedValue_natural_of_eq _ _ (cyclicSchemeValue_base n f c)
      k _ _ (cyclicSchemeValue_base n (k ≫ f) c)
      (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Sourcewise normalization is exactly composition with the actual global full morphism. -/
theorem cyclicSchemeNormalizedPoint_eq_comp :
    cyclicSchemeNormalizedPoint n f = f ≫ cyclicNormalizationMap n := by
  simpa only [Category.comp_id, cyclicNormalizationMap] using
    cyclicSchemeNormalizedPoint_natural n (𝟙 _) f

/-- The independently constructed full closed-slice lift is natural on arbitrary schemes. -/
theorem cyclicSchemeNormalizedSlicePoint_natural (k : U ⟶ T) :
    cyclicSchemeNormalizedSlicePoint n (k ≫ f) = k ≫ cyclicSchemeNormalizedSlicePoint n f := by
  apply (cancel_mono (cyclicNormalizedSliceInclusion n)).mp
  rw [Category.assoc, cyclicSchemeNormalizedSlicePoint_inclusion,
    cyclicSchemeNormalizedSlicePoint_inclusion, cyclicSchemeNormalizedPoint_natural]

/-- The independent full closed-slice lift is exactly its natural global family. -/
theorem cyclicSchemeNormalizedSlicePoint_eq_natural :
    cyclicSchemeNormalizedSlicePoint n f = cyclicNaturalNormalizedSlicePoint n f := by
  apply (cancel_mono (cyclicNormalizedSliceInclusion n)).mp
  rw [cyclicSchemeNormalizedSlicePoint_inclusion, cyclicNaturalNormalizedSlicePoint_inclusion,
    cyclicSchemeNormalizedPoint_eq_comp]

end FLT.Mazur.UniversalWeierstrass
