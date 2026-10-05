/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorIdealEvaluation
public import FLT.Mazur.IdealQuotientExact
public import FLT.Mazur.ModuleLineTensorExact

/-!
# Tensoring the ideal sequence by the divisor line

The canonical contraction intertwines the tensorized ideal inclusion with
O → O(D). Thus its cokernel is the tensor of the actual closed quotient with O(D).
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor

variable {X : Scheme.{u}} {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- Contraction carries the ideal inclusion to the actual canonical divisor section. -/
lemma divisorIdealEvaluation_section :
    divisorIdealEvaluation hI ≫ divisorSectionMap hI =
      map (idealModuleι I) (𝟙 _) ≫ (leftUnitor (divisorLineBundle I hI)).hom := by
  apply (SheafOfModules.toSheaf X.ringCatSheaf).map_injective
  apply CategoryTheory.Sheaf.hom_ext
  apply (TopCat.Sheaf.restrictHomEquivHom _ _
    (commonCartierChart_isBasis hI hI)).symm.injective
  ext U : 2
  let V := U.unop.1
  have hV := U.unop.2.1
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  let M := idealModule I
  let N := divisorLineBundle I hI
  let c := hV.idealTrivialization
  let d := hV.divisorTrivialization hI
  have hc : (unit (M.restrict V.1.ι) (N.restrict V.1.ι)).app (op ⊤) =
      ModuleCat.ofHom (trivialSectionsEquiv c d ⊤).toLinearMap := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    exact (trivialSectionsEquiv_tmul c d ⊤ m n).symm
  have ht := unit_image_bijective M N V.1.ι ⊤
    (by rw [hc]; exact (trivialSectionsEquiv c d ⊤).bijective)
  rw [Scheme.Opens.ι_image_top] at ht
  obtain ⟨z, rfl⟩ := ht.2 z
  induction z using TensorProduct.inductionOn with
  | tmul s φ =>
    change (divisorSectionMap hI).app V.1
      ((divisorIdealEvaluation hI).app V.1 (pure _ _ _ s φ)) =
        (leftUnitor N).hom.app V.1 ((map (idealModuleι I) (𝟙 N)).app V.1
          (pure _ _ _ s φ))
    rw [divisorIdealEvaluation_pure, map_pure]
    erw [leftUnitor_pure N V.1 ((idealModuleι I).app V.1 s)
      (Scheme.Modules.Hom.app (𝟙 N) V.1 φ)]
    apply ((hV.divisorSectionsEquiv hI).trans hV.dualEquiv).injective
    change hV.dualEquiv (divisorChartEval I V
      ((divisorSectionMap hI).app V.1 (moduleDualEval (idealModule I) V.1 φ s))) = _
    rw [divisorSectionMap_coordinate]
    simp only [Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply, map_smul]
    rw [← idealModuleAffineEquiv_val]
    obtain ⟨r, hr⟩ := hV.idealEquiv.surjective (idealModuleAffineEquiv I V s)
    have he : moduleDualEval (idealModule I) V.1 φ s =
        r * hV.dualEquiv (divisorChartEval I V φ) := by
      have hs : s = r • (idealModuleAffineEquiv I V).symm (hV.idealEquiv 1) := by
        apply (idealModuleAffineEquiv I V).injective
        rw [map_smul, LinearEquiv.apply_symm_apply, ← map_smul]
        simpa using hr.symm
      rw [hs, map_smul]
      rfl
    rw [he, ← hr]
    change (r * _) * hV.choose = (r * hV.choose) * _
    exact mul_right_comm r _ _
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

/-- Tensoring the actual ideal sequence with its divisor line preserves short exactness. -/
theorem divisorTensorSequence_shortExact :
    ((idealQuotientComplex I).map
      (ModuleSheafTensorCurrying.tensoring (divisorLineBundle I hI))).ShortExact :=
  ModuleLineTensorExact.shortExact _ (idealQuotientComplex_shortExact I) _
    hI.divisorLineBundle_locallyFreeRankOne

end FLT.Mazur.FCurve
