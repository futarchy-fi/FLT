/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdditiveComplexSumHomology

/-!
# Naturality of the integral homology comparison

The additive cycle and quotient maps also give integral linear maps. This
identifies the action on homology without changing either chosen comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace FLT.Mazur.AdditiveComplexDirectSum

variable {S T : ShortComplex AddCommGrpCat.{0}}

/-- An original additive morphism with its canonical integral linear structure. -/
def integralShortMap (φ : S ⟶ T) : integralShort S ⟶ integralShort T where
  τ₁ := ModuleCat.ofHom φ.τ₁.hom.toIntLinearMap
  τ₂ := ModuleCat.ofHom φ.τ₂.hom.toIntLinearMap
  τ₃ := ModuleCat.ofHom φ.τ₃.hom.toIntLinearMap
  comm₁₂ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom φ.comm₁₂ x
  comm₂₃ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom φ.comm₂₃ x

/-- The additive cycles and quotient maps remain the actual integral homology data. -/
def integralHomologyMapData (φ : S ⟶ T) :
    ShortComplex.LeftHomologyMapData (integralShortMap φ)
      (integralShort S).moduleCatLeftHomologyData
      (integralShort T).moduleCatLeftHomologyData where
  φK := ModuleCat.ofHom
    (ShortComplex.leftHomologyMapData φ
      S.abLeftHomologyData T.abLeftHomologyData).φK.hom.toIntLinearMap
  φH := ModuleCat.ofHom
    (ShortComplex.leftHomologyMapData φ
      S.abLeftHomologyData T.abLeftHomologyData).φH.hom.toIntLinearMap
  commi := by
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom
      (ShortComplex.leftHomologyMapData φ S.abLeftHomologyData T.abLeftHomologyData).commi x
  commf' := by
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom
      (ShortComplex.leftHomologyMapData φ S.abLeftHomologyData T.abLeftHomologyData).commf' x
  commπ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom
      (ShortComplex.leftHomologyMapData φ S.abLeftHomologyData T.abLeftHomologyData).commπ x

/-- Integral and additive homology comparisons commute with every original short-complex map. -/
lemma integralHomologyEquiv_naturality (φ : S ⟶ T) (x : S.homology) :
    integralHomologyEquiv T (ShortComplex.homologyMap φ x) =
      ShortComplex.homologyMap (integralShortMap φ) (integralHomologyEquiv S x) := by
  have ha := ConcreteCategory.congr_hom
    (ShortComplex.leftHomologyMapData φ
      S.abLeftHomologyData T.abLeftHomologyData).homologyMap_comm x
  have hi := ConcreteCategory.congr_hom
    (integralHomologyMapData φ).homologyMap_comm (integralHomologyEquiv S x)
  simp only [ConcreteCategory.comp_apply] at ha hi
  apply (ModuleCat.mono_iff_injective
    (integralShort T).moduleCatHomologyIso.hom).mp inferInstance
  change (integralShort T).moduleCatHomologyIso.hom
    ((integralShort T).moduleCatHomologyIso.inv
      (T.abHomologyIso.hom (ShortComplex.homologyMap φ x))) = _
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  refine Eq.trans ?_ hi.symm
  change T.abHomologyIso.hom (ShortComplex.homologyMap φ x) =
    (ShortComplex.leftHomologyMapData φ S.abLeftHomologyData T.abLeftHomologyData).φH
      ((integralShort S).moduleCatHomologyIso.hom
        ((integralShort S).moduleCatHomologyIso.inv (S.abHomologyIso.hom x)))
  simp only [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]
  exact ha

end FLT.Mazur.AdditiveComplexDirectSum
