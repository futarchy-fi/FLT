/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundleRestrict
public import FLT.Mazur.ModuleSheafTensorAffineOpen

/-!
# Global sum comparison for divisor line bundles

On common Cartier charts, sections of the actual sheaf tensor identify with
sections of the positive line bundle of the product ideal. The comparison is
canonical on pure tensors and commutes with restriction between these charts.
Basis extension gives a global module-sheaf isomorphism without added hypotheses.
Coherence with open-subscheme comparisons and the empty divisor remains separate.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}} {I J : X.IdealSheafData}

/-- On a common trivializing open, the tensor sheaf has the expected sections. -/
lemma CartierChart.tensorUnit_bijective {U : X.affineOpens}
    (hU : CartierChart I U) (hV : CartierChart J U)
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) :
    Function.Bijective ((ModuleSheafTensor.unit
      (divisorLineBundle I hI) (divisorLineBundle J hJ)).app (op U.1)) := by
  let M := divisorLineBundle I hI
  let N := divisorLineBundle J hJ
  let e := hU.divisorTrivialization hI
  let f := hV.divisorTrivialization hJ
  have he : (ModuleSheafTensor.unit (M.restrict U.1.ι) (N.restrict U.1.ι)).app
      (op ⊤) = ModuleCat.ofHom (ModuleSheafTensor.trivialSectionsEquiv e f ⊤).toLinearMap := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    exact (ModuleSheafTensor.trivialSectionsEquiv_tmul e f ⊤ m n).symm
  have hb := ModuleSheafTensor.unit_image_bijective M N U.1.ι ⊤
    (by rw [he]; exact (ModuleSheafTensor.trivialSectionsEquiv e f ⊤).bijective)
  rwa [Scheme.Opens.ι_image_top] at hb

/-- The canonical tensor-section map on a common Cartier chart. -/
def CartierChart.tensorSectionsEquiv {U : X.affineOpens}
    (hU : CartierChart I U) (hV : CartierChart J U)
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) :
    Γ(divisorLineBundle I hI, U.1) ⊗[Γ(X, U)] Γ(divisorLineBundle J hJ, U.1) ≃ₗ[Γ(X, U)]
      Γ(ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ), U.1) :=
  LinearEquiv.ofBijective ((ModuleSheafTensor.unit
    (divisorLineBundle I hI) (divisorLineBundle J hJ)).app (op U.1)).hom
      (hU.tensorUnit_bijective hV hI hJ)

@[simp]
lemma CartierChart.tensorSectionsEquiv_tmul {U : X.affineOpens}
    (hU : CartierChart I U) (hV : CartierChart J U)
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (s : Γ(divisorLineBundle I hI, U.1)) (t : Γ(divisorLineBundle J hJ, U.1)) :
    hU.tensorSectionsEquiv hV hI hJ (s ⊗ₜ t) =
      ModuleSheafTensor.pure (divisorLineBundle I hI) (divisorLineBundle J hJ) U.1 s t := rfl

/-- The chart sum comparison on sections of the actual sheaf tensor. -/
def CartierChart.lineBundleSumSectionsEquiv {U : X.affineOpens}
    (hU : CartierChart I U) (hV : CartierChart J U)
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) :
    Γ(ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ), U.1)
      ≃ₗ[Γ(X, U)] Γ(divisorLineBundle (I * J) (hI.mul hJ), U.1) :=
  (hU.tensorSectionsEquiv hV hI hJ).symm ≪≫ₗ
    TensorProduct.congr (hU.divisorSectionsEquiv hI) (hV.divisorSectionsEquiv hJ) ≪≫ₗ
      hU.sumEquiv hV ≪≫ₗ ((hU.mul hV).divisorSectionsEquiv (hI.mul hJ)).symm

/-- The section comparison agrees with the dual-ideal sum map on pure tensors. -/
lemma CartierChart.lineBundleSumSectionsEquiv_pure {U : X.affineOpens}
    (hU : CartierChart I U) (hV : CartierChart J U)
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (s : Γ(divisorLineBundle I hI, U.1)) (t : Γ(divisorLineBundle J hJ, U.1)) :
    (hU.mul hV).divisorSectionsEquiv (hI.mul hJ)
      (hU.lineBundleSumSectionsEquiv hV hI hJ
        (ModuleSheafTensor.pure (divisorLineBundle I hI) (divisorLineBundle J hJ) U.1 s t)) =
      hU.sumEquiv hV (hU.divisorSectionsEquiv hI s ⊗ₜ hV.divisorSectionsEquiv hJ t) := by
  rw [← CartierChart.tensorSectionsEquiv_tmul hU hV hI hJ]
  simp only [lineBundleSumSectionsEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply, TensorProduct.congr_tmul]

/-- Evaluation on a product is multiplication of the two original evaluations. -/
lemma CartierChart.lineBundleSumSectionsEquiv_eval {U : X.affineOpens}
    (hU : CartierChart I U) (hV : CartierChart J U)
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (s : Γ(divisorLineBundle I hI, U.1)) (t : Γ(divisorLineBundle J hJ, U.1))
    (x : I.ideal U) (y : J.ideal U) :
    divisorChartEval (I * J) U
      (hU.lineBundleSumSectionsEquiv hV hI hJ
        (ModuleSheafTensor.pure (divisorLineBundle I hI) (divisorLineBundle J hJ) U.1 s t))
      ⟨(x : Γ(X, U)) * y, Ideal.mul_mem_mul x.property y.property⟩ =
        divisorChartEval I U s x * divisorChartEval J U t y := by
  exact (congrArg (fun f ↦ f ⟨(x : Γ(X, U)) * y,
    Ideal.mul_mem_mul x.property y.property⟩)
    (hU.lineBundleSumSectionsEquiv_pure hV hI hJ s t)).trans
      (hU.sumEquiv_apply hV _ _ x y)

/-- The sum comparisons commute with restriction on all tensor-sheaf sections. -/
lemma CartierChart.lineBundleSumSectionsEquiv_restrict {U V : X.affineOpens}
    (hU : CartierChart I V) (hV : CartierChart J V)
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) (h : U ≤ V)
    (z : Γ(ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ), V.1)) :
    (hU.mono h).lineBundleSumSectionsEquiv (hV.mono h) hI hJ
      ((ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ)).presheaf.map
        (homOfLE (show U.1 ≤ V.1 from h)).op z) =
      (divisorLineBundle (I * J) (hI.mul hJ)).presheaf.map
        (homOfLE (show U.1 ≤ V.1 from h)).op
          (hU.lineBundleSumSectionsEquiv hV hI hJ z) := by
  obtain ⟨z, rfl⟩ := (hU.tensorSectionsEquiv hV hI hJ).surjective z
  induction z using TensorProduct.inductionOn with
  | tmul s t =>
    rw [CartierChart.tensorSectionsEquiv_tmul, ModuleSheafTensor.pure_restrict]
    apply (((hU.mono h).mul (hV.mono h)).divisorSectionsEquiv (hI.mul hJ)).injective
    rw [CartierChart.lineBundleSumSectionsEquiv_pure,
      CartierChart.divisorSectionsEquiv_restrict (hU.mul hV) _ _ h,
      CartierChart.lineBundleSumSectionsEquiv_pure,
      CartierChart.divisorSectionsEquiv_restrict hU _ _ h,
      CartierChart.divisorSectionsEquiv_restrict hV _ _ h,
      CartierChart.dualRestrict_sumEquiv]
  | add z w hz hw =>
    rw [(hU.tensorSectionsEquiv hV hI hJ).map_add z w]
    simp only [map_add, hz, hw]

/-- Common Cartier charts, with their inclusions into the open-set category. -/
abbrev CommonCartierChart (I J : X.IdealSheafData) :=
  {U : X.affineOpens // CartierChart I U ∧ CartierChart J U}

/-- Common Cartier charts form a basis, including inside every prescribed open. -/
lemma commonCartierChart_isBasis (hI : EffectiveCartier I) (hJ : EffectiveCartier J) :
    TopologicalSpace.Opens.IsBasis
      (Set.range (fun U : CommonCartierChart I J ↦ U.1.1)) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro W x hx
  obtain ⟨V, hxV, hVW, hV⟩ := hI.exists_chart_le hx
  obtain ⟨U, hxU, hUV, hU⟩ := hJ.exists_chart_le hxV
  exact ⟨U.1, ⟨⟨U, hV.mono hUV, hU⟩, rfl⟩, hxU, hUV.trans hVW⟩

/-- The additive sum map on the basis of common Cartier charts. -/
def divisorLineBundleSumBasis (hI : EffectiveCartier I) (hJ : EffectiveCartier J) :
    (inducedFunctor (fun U : CommonCartierChart I J ↦ U.1.1)).op ⋙
        (ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ)).presheaf ⟶
      (inducedFunctor (fun U : CommonCartierChart I J ↦ U.1.1)).op ⋙
        (divisorLineBundle (I * J) (hI.mul hJ)).presheaf where
  app U := AddCommGrpCat.ofHom
    (U.unop.2.1.lineBundleSumSectionsEquiv U.unop.2.2 hI hJ).toAddMonoidHom
  naturality {U V} i := by
    apply ConcreteCategory.hom_ext
    intro z
    change V.unop.2.1.lineBundleSumSectionsEquiv V.unop.2.2 hI hJ
      ((ModuleSheafTensor.tensor (divisorLineBundle I hI)
        (divisorLineBundle J hJ)).presheaf.map
          ((inducedFunctor (fun U : CommonCartierChart I J ↦ U.1.1)).map i.unop).op z) = _
    exact (U.unop.2.1.lineBundleSumSectionsEquiv_restrict U.unop.2.2 hI hJ
      (show V.unop.1 ≤ U.unop.1 from
        leOfHom ((inducedFunctor (fun U : CommonCartierChart I J ↦ U.1.1)).map i.unop)) z)

/-- Extend the additive comparison from the common Cartier basis. -/
def divisorLineBundleSumAddHom (hI : EffectiveCartier I) (hJ : EffectiveCartier J) :
    (ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ)).presheaf ⟶
      (divisorLineBundle (I * J) (hI.mul hJ)).presheaf :=
  TopCat.Sheaf.restrictHomEquivHom _
    ((SheafOfModules.toSheaf _).obj (divisorLineBundle (I * J) (hI.mul hJ)))
    (commonCartierChart_isBasis hI hJ) (divisorLineBundleSumBasis hI hJ)

lemma divisorLineBundleSumAddHom_app (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (U : CommonCartierChart I J) :
    (divisorLineBundleSumAddHom hI hJ).app (op U.1.1) =
      AddCommGrpCat.ofHom (U.2.1.lineBundleSumSectionsEquiv U.2.2 hI hJ).toAddMonoidHom :=
  TopCat.Sheaf.extend_hom_app _ _ (commonCartierChart_isBasis hI hJ) _ U

/-- The extended additive comparison is linear over the structure sheaf. -/
def divisorLineBundleSumHom (hI : EffectiveCartier I) (hJ : EffectiveCartier J) :
    ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ) ⟶
      divisorLineBundle (I * J) (hI.mul hJ) := by
  let M := ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ)
  let P := divisorLineBundle (I * J) (hI.mul hJ)
  let f := divisorLineBundleSumAddHom hI hJ
  refine ⟨PresheafOfModules.homMk f ?_⟩
  intro W r s
  change Γ(X, W.unop) at r
  change Γ(M, W.unop) at s
  apply TopCat.Presheaf.IsSheaf.section_ext P.isSheaf
  intro x hx
  obtain ⟨V, ⟨U, rfl⟩, hxU, hUW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (commonCartierChart_isBasis hI hJ) hx
  refine ⟨U.1.1, hUW, hxU, ?_⟩
  have hn (t : Γ(M, W.unop)) :
      P.presheaf.map (homOfLE hUW).op (f.app W t) =
        f.app (op U.1.1) (M.presheaf.map (homOfLE hUW).op t) :=
    (congr($(f.naturality (homOfLE hUW).op) t)).symm
  change P.presheaf.map (homOfLE hUW).op (f.app W (r • s)) =
    P.presheaf.map (homOfLE hUW).op (r • (show Γ(P, W.unop) from f.app W s))
  rw [Scheme.Modules.map_smul, hn, Scheme.Modules.map_smul, hn]
  dsimp only [f]
  rw [divisorLineBundleSumAddHom_app]
  exact (U.2.1.lineBundleSumSectionsEquiv U.2.2 hI hJ).map_smul _ _

lemma divisorLineBundleSumHom_app (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (U : CommonCartierChart I J) (z) :
    (divisorLineBundleSumHom hI hJ).app U.1.1 z =
      U.2.1.lineBundleSumSectionsEquiv U.2.2 hI hJ z := by
  change (divisorLineBundleSumAddHom hI hJ).app (op U.1.1) z = _
  rw [divisorLineBundleSumAddHom_app]
  rfl

instance divisorLineBundleSumHom_isIso (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) : IsIso (divisorLineBundleSumHom hI hJ) := by
  let f := (SheafOfModules.toSheaf _).map (divisorLineBundleSumHom hI hJ)
  have hf : IsIso f := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (commonCartierChart_isBasis hI hJ)
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective ((divisorLineBundleSumHom hI hJ).app U.1.1)
    simp only [Function.Bijective, Function.Injective, Function.Surjective,
      divisorLineBundleSumHom_app]
    exact (U.2.1.lineBundleSumSectionsEquiv U.2.2 hI hJ).bijective
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  exact inferInstanceAs (IsIso (f.hom.app (op U)))

/-- The tensor of the actual positive divisor sheaves is the sheaf of their sum. -/
def divisorLineBundleSumIso (hI : EffectiveCartier I) (hJ : EffectiveCartier J) :
    ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ) ≅
      divisorLineBundle (I * J) (hI.mul hJ) :=
  asIso (divisorLineBundleSumHom hI hJ)

/-- The global comparison is the prescribed chart sum, evaluated on actual ideal products. -/
lemma divisorLineBundleSumIso_eval (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (U : X.affineOpens) (hU : CartierChart I U) (hV : CartierChart J U)
    (s : Γ(divisorLineBundle I hI, U.1)) (t : Γ(divisorLineBundle J hJ, U.1))
    (x : I.ideal U) (y : J.ideal U) :
    divisorChartEval (I * J) U ((divisorLineBundleSumIso hI hJ).hom.app U.1
      (ModuleSheafTensor.pure (divisorLineBundle I hI) (divisorLineBundle J hJ) U.1 s t))
      ⟨(x : Γ(X, U)) * y, Ideal.mul_mem_mul x.property y.property⟩ =
        divisorChartEval I U s x * divisorChartEval J U t y := by
  change divisorChartEval (I * J) U ((divisorLineBundleSumHom hI hJ).app U.1 _) _ = _
  rw [divisorLineBundleSumHom_app hI hJ ⟨U, hU, hV⟩]
  exact hU.lineBundleSumSectionsEquiv_eval hV hI hJ s t x y

end FLT.Mazur.FCurve
