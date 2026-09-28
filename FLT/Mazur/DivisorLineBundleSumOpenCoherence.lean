/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundleSumRestrict

/-!
# Open restriction of the divisor sum comparison

The chart product calculation identifies restriction of the global sum with the
sum of the restricted divisors. Equality on a common Cartier basis gives the
commuting diagram for the actual tensor and divisor sheaves.

Typed section functions keep the kernel from unfolding the canonical target
identification while comparing evaluations.
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

/-- The global sum gives the prescribed dual-ideal sum on a common chart. -/
lemma divisorLineBundleSumIso_chart (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (V : X.affineOpens) (hW : CartierChart I V) (hV : CartierChart J V)
    (s : Γ(divisorLineBundle I hI, V.1)) (t : Γ(divisorLineBundle J hJ, V.1)) :
    (hW.mul hV).divisorSectionsEquiv (hI.mul hJ)
      ((divisorLineBundleSumIso hI hJ).hom.app V.1
        (ModuleSheafTensor.pure (divisorLineBundle I hI) (divisorLineBundle J hJ) V.1 s t)) =
      hW.sumEquiv hV (hW.divisorSectionsEquiv hI s ⊗ₜ hV.divisorSectionsEquiv hJ t) := by
  apply hW.dual_ext_products hV
  intro x y
  exact (divisorLineBundleSumIso_eval hI hJ V hW hV s t x y).trans
    (hW.sumEquiv_apply hV _ _ x y).symm

/-- Restriction of the global sum has the transported chart value. -/
lemma divisorLineBundleSumRestrict_chart (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) (U : X.Opens) (W : U.toScheme.affineOpens)
    (hW : CartierChart I ⟨U.ι ''ᵁ W, W.2.image_of_isOpenImmersion U.ι⟩)
    (hV : CartierChart J ⟨U.ι ''ᵁ W, W.2.image_of_isOpenImmersion U.ι⟩)
    (hP : CartierChart ((I * J).comap U.ι) W)
    (s : Γ(divisorLineBundle I hI, U.ι ''ᵁ W))
    (t : Γ(divisorLineBundle J hJ, U.ι ''ᵁ W)) :
    hP.divisorSectionsEquiv ((hI.mul hJ).comap_of_isOpenImmersion U.ι)
      ((divisorLineBundleRestrictIso (I * J) (hI.mul hJ) U).hom.app W.1
        (((divisorLineBundle (I * J) (hI.mul hJ)).restrictAppIso U.ι W.1).inv
          ((divisorLineBundleSumIso hI hJ).hom.app (U.ι ''ᵁ W)
            (ModuleSheafTensor.pure (divisorLineBundle I hI) (divisorLineBundle J hJ)
              (U.ι ''ᵁ W) s t)))) =
      divisorChartTransport (I * J) U.ι W
        (hW.sumEquiv hV (hW.divisorSectionsEquiv hI s ⊗ₜ hV.divisorSectionsEquiv hJ t)) := by
  exact (divisorLineBundleRestrictIso_chartTransport_inv (hI.mul hJ) U W (hW.mul hV) hP
    ((divisorLineBundleSumIso hI hJ).hom.app (U.ι ''ᵁ W)
      (ModuleSheafTensor.pure (divisorLineBundle I hI) (divisorLineBundle J hJ)
        (U.ι ''ᵁ W) s t))).trans
    (congrArg (divisorChartTransport (I * J) U.ι W)
      (divisorLineBundleSumIso_chart hI hJ _ hW hV s t))

/-- Unfold the open sum before evaluating sections. -/
lemma divisorLineBundleSumOnIso_def (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (U : X.Opens) :
    divisorLineBundleSumOnIso hI hJ U =
      divisorLineBundleSumIso (hI.comap_of_isOpenImmersion U.ι)
          (hJ.comap_of_isOpenImmersion U.ι) ≪≫
        divisorLineBundleCongr (idealSheaf_comap_mul I J U.ι).symm
          ((hI.comap_of_isOpenImmersion U.ι).mul
            (hJ.comap_of_isOpenImmersion U.ι))
          ((hI.mul hJ).comap_of_isOpenImmersion U.ι) := rfl

/-- An identified canonical sum isomorphism has the product-evaluation formula. -/
lemma divisorLineBundleSumCongr_iso_eval {K : X.IdealSheafData}
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) (hK : EffectiveCartier K)
    (e : I * J = K)
    (E : ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ) ≅
      divisorLineBundle K hK)
    (hE : E = divisorLineBundleSumIso hI hJ ≪≫ divisorLineBundleCongr e (hI.mul hJ) hK)
    (W : X.affineOpens) (hW : CartierChart I W) (hV : CartierChart J W)
    (hP : CartierChart K W)
    (s : Γ(divisorLineBundle I hI, W.1)) (t : Γ(divisorLineBundle J hJ, W.1))
    (x : I.ideal W) (y : J.ideal W) (z : K.ideal W)
    (hxy : (x : Γ(X, W)) * y = z) :
    hP.divisorSectionsEquiv hK
      (E.hom.app W.1 (ModuleSheafTensor.pure (divisorLineBundle I hI)
        (divisorLineBundle J hJ) W.1 s t)) z =
      hW.divisorSectionsEquiv hI s x * hV.divisorSectionsEquiv hJ t y := by
  subst E
  exact divisorLineBundleSumCongr_eval hI hJ hK e W hW hV hP s t x y z hxy

/-- Evaluation as a function on actual divisor sections. -/
def divisorSectionPairing (I : X.IdealSheafData) (hI : EffectiveCartier I)
    (W : X.affineOpens) (s : Γ(divisorLineBundle I hI, W.1))
    (x : I.ideal W) : Γ(X, W) := divisorChartEval I W s x

/-- Apply an isomorphism from the actual tensor to a pure section. -/
def divisorSumSection {K : X.IdealSheafData}
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) (hK : EffectiveCartier K)
    (E : ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ) ≅
      divisorLineBundle K hK) (W : X.affineOpens)
    (s : Γ(divisorLineBundle I hI, W.1)) (t : Γ(divisorLineBundle J hJ, W.1)) :
    Γ(divisorLineBundle K hK, W.1) :=
  E.hom.app W.1 (ModuleSheafTensor.pure (divisorLineBundle I hI)
    (divisorLineBundle J hJ) W.1 s t)

/-- An identified canonical sum isomorphism has the product-evaluation formula. -/
lemma divisorLineBundleSumCongr_pairing {K : X.IdealSheafData}
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) (hK : EffectiveCartier K)
    (e : I * J = K)
    (E : ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ) ≅
      divisorLineBundle K hK)
    (hE : E = divisorLineBundleSumIso hI hJ ≪≫ divisorLineBundleCongr e (hI.mul hJ) hK)
    (W : X.affineOpens) (hW : CartierChart I W) (hV : CartierChart J W)
    (hP : CartierChart K W)
    (s : Γ(divisorLineBundle I hI, W.1)) (t : Γ(divisorLineBundle J hJ, W.1))
    (x : I.ideal W) (y : J.ideal W) (z : K.ideal W)
    (hxy : (x : Γ(X, W)) * y = z) :
    divisorSectionPairing K hK W
      (divisorSumSection hI hJ hK E W s t) z =
      divisorSectionPairing I hI W s x * divisorSectionPairing J hJ W t y := by
  exact divisorLineBundleSumCongr_iso_eval hI hJ hK e E hE W hW hV hP s t x y z hxy

/-- The canonical target identification preserves evaluation of the open sum. -/
lemma divisorLineBundleSumOnIso_eval (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) (U : X.Opens) (W : U.toScheme.affineOpens)
    (hW : CartierChart (I.comap U.ι) W) (hV : CartierChart (J.comap U.ι) W)
    (hP : CartierChart ((I * J).comap U.ι) W)
    (s : Γ(divisorLineBundleOn I hI U, W.1))
    (t : Γ(divisorLineBundleOn J hJ U, W.1))
    (x : (I.comap U.ι).ideal W) (y : (J.comap U.ι).ideal W)
    (z : ((I * J).comap U.ι).ideal W) (hxy : (x : Γ(U.toScheme, W)) * y = z) :
    divisorSectionPairing ((I * J).comap U.ι)
      ((hI.mul hJ).comap_of_isOpenImmersion U.ι) W
      (divisorSumSection (hI.comap_of_isOpenImmersion U.ι)
        (hJ.comap_of_isOpenImmersion U.ι) ((hI.mul hJ).comap_of_isOpenImmersion U.ι)
        (divisorLineBundleSumOnIso hI hJ U) W s t) z =
      divisorSectionPairing (I.comap U.ι) (hI.comap_of_isOpenImmersion U.ι) W s x *
        divisorSectionPairing (J.comap U.ι) (hJ.comap_of_isOpenImmersion U.ι) W t y := by
  exact divisorLineBundleSumCongr_pairing (X := U.toScheme)
    (I := I.comap U.ι) (J := J.comap U.ι) (K := (I * J).comap U.ι)
    (hI.comap_of_isOpenImmersion U.ι) (hJ.comap_of_isOpenImmersion U.ι)
    ((hI.mul hJ).comap_of_isOpenImmersion U.ι) (idealSheaf_comap_mul I J U.ι).symm
    (divisorLineBundleSumOnIso hI hJ U) (divisorLineBundleSumOnIso_def hI hJ U)
    W hW hV hP s t x y z hxy

/-- Restriction transports the pairing of actual divisor sections. -/
lemma divisorLineBundleRestrict_pairing (hI : EffectiveCartier I)
    (U : X.Opens) (W : U.toScheme.affineOpens)
    (hW : CartierChart I ⟨U.ι ''ᵁ W, W.2.image_of_isOpenImmersion U.ι⟩)
    (s : Γ(divisorLineBundle I hI, U.ι ''ᵁ W)) (x : (I.comap U.ι).ideal W) :
    divisorSectionPairing (I.comap U.ι) (hI.comap_of_isOpenImmersion U.ι) W
      ((divisorLineBundleRestrictIso I hI U).hom.app W.1
        (((divisorLineBundle I hI).restrictAppIso U.ι W.1).inv s)) x =
      divisorChartTransport I U.ι W (hW.divisorSectionsEquiv hI s) x := by
  exact DFunLike.congr_fun (divisorLineBundleRestrictIso_chartTransport_inv hI U W hW
    ((cartierChart_comap_iff I U.ι W).mpr hW) s) x

/-- Chart sums commute with the canonical divisor restrictions. -/
lemma divisorLineBundleSumRestrict_sections (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) (U : X.Opens) (W : U.toScheme.affineOpens)
    (hW : CartierChart I ⟨U.ι ''ᵁ W, W.2.image_of_isOpenImmersion U.ι⟩)
    (hV : CartierChart J ⟨U.ι ''ᵁ W, W.2.image_of_isOpenImmersion U.ι⟩)
    (s : Γ(divisorLineBundle I hI, U.ι ''ᵁ W))
    (t : Γ(divisorLineBundle J hJ, U.ι ''ᵁ W)) :
    ((divisorLineBundleRestrictIso (I * J) (hI.mul hJ) U).hom.app (X := U.toScheme) W.1
      (((divisorLineBundle (I * J) (hI.mul hJ)).restrictAppIso U.ι W.1).inv
        ((divisorLineBundleSumIso hI hJ).hom.app (U.ι ''ᵁ W)
          (ModuleSheafTensor.pure (divisorLineBundle I hI) (divisorLineBundle J hJ)
            (U.ι ''ᵁ W) s t))) :
      Γ(divisorLineBundleOn (I * J) (hI.mul hJ) U, W.1)) =
      divisorSumSection (hI.comap_of_isOpenImmersion U.ι)
        (hJ.comap_of_isOpenImmersion U.ι) ((hI.mul hJ).comap_of_isOpenImmersion U.ι)
        (divisorLineBundleSumOnIso hI hJ U) W
        ((divisorLineBundleRestrictIso I hI U).hom.app (X := U.toScheme) W.1
          (((divisorLineBundle I hI).restrictAppIso U.ι W.1).inv s))
        ((divisorLineBundleRestrictIso J hJ U).hom.app (X := U.toScheme) W.1
          (((divisorLineBundle J hJ).restrictAppIso U.ι W.1).inv t)) := by
  have hP : CartierChart ((I * J).comap U.ι) W :=
    (cartierChart_comap_iff (I * J) U.ι W).mpr (hW.mul hV)
  apply (hP.divisorSectionsEquiv ((hI.mul hJ).comap_of_isOpenImmersion U.ι)).injective
  rw [divisorLineBundleSumRestrict_chart hI hJ U W hW hV hP]
  apply divisorChartTransport_dual_ext_products U.ι W hW hV
  intro x y
  let x' := CartierModule.idealRestrict _ _ _ (ideal_map_appIso I U.ι W).le x
  let y' := CartierModule.idealRestrict _ _ _ (ideal_map_appIso J U.ι W).le y
  let z' := CartierModule.idealRestrict _ _ _ (ideal_map_appIso (I * J) U.ι W).le
    ⟨(x : Γ(X, U.ι ''ᵁ W)) * y, Ideal.mul_mem_mul x.property y.property⟩
  have hz : (x' : Γ(U.toScheme, W)) * y' = z' :=
    (map_mul (U.ι.appIso W).hom.hom (x : Γ(X, U.ι ''ᵁ W)) y).symm
  rw [divisorChartTransport_sum_eval U.ι W hW hV]
  change _ = divisorSectionPairing ((I * J).comap U.ι)
    ((hI.mul hJ).comap_of_isOpenImmersion U.ι) W
    (divisorSumSection _ _ _ (divisorLineBundleSumOnIso hI hJ U) W _ _) z'
  rw [divisorLineBundleSumOnIso_eval hI hJ U W
    ((cartierChart_comap_iff I U.ι W).mpr hW)
    ((cartierChart_comap_iff J U.ι W).mpr hV) hP _ _ x' y' z' hz]
  exact congrArg₂ (fun (a b : Γ(U.toScheme, W)) ↦ a * b)
    (divisorLineBundleRestrict_pairing hI U W hW s x').symm
    (divisorLineBundleRestrict_pairing hJ U W hV t y').symm

/-- Apply a module-sheaf morphism through its section function. -/
def moduleSectionApply {M N : X.Modules} (a : M ⟶ N) (W : X.Opens)
    (s : Γ(M, W)) : Γ(N, W) := a.app W s

lemma moduleSectionApply_add {M N : X.Modules} (a : M ⟶ N) (W : X.Opens)
    (s t : Γ(M, W)) :
    moduleSectionApply a W (s + t) = moduleSectionApply a W s + moduleSectionApply a W t :=
  map_add (a.app W).hom s t

/-- Composition with a tensor comparison evaluates through its typed section map. -/
lemma divisorSumSection_comp {K : X.IdealSheafData} {M : X.Modules}
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) (hK : EffectiveCartier K)
    (E : ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ) ≅
      divisorLineBundle K hK)
    (a : M ⟶ ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ))
    (W : X.affineOpens) (z : Γ(M, W.1))
    (s : Γ(divisorLineBundle I hI, W.1)) (t : Γ(divisorLineBundle J hJ, W.1))
    (ha : a.app W.1 z = ModuleSheafTensor.pure (divisorLineBundle I hI)
      (divisorLineBundle J hJ) W.1 s t) :
    moduleSectionApply (a ≫ E.hom) W.1 z = divisorSumSection hI hJ hK E W s t := by
  exact congrArg (E.hom.app W.1) ha

/-- The restriction diagram commutes on pure sections of a common Cartier chart. -/
lemma divisorLineBundleSumRestrict_pure (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) (U : X.Opens) (W : U.toScheme.affineOpens)
    (hW : CartierChart I ⟨U.ι ''ᵁ W, W.2.image_of_isOpenImmersion U.ι⟩)
    (hV : CartierChart J ⟨U.ι ''ᵁ W, W.2.image_of_isOpenImmersion U.ι⟩)
    (s : Γ(divisorLineBundle I hI, U.ι ''ᵁ W))
    (t : Γ(divisorLineBundle J hJ, U.ι ''ᵁ W)) :
    moduleSectionApply ((Scheme.Modules.restrictFunctor U.ι).map
        (divisorLineBundleSumIso hI hJ).hom ≫
        (divisorLineBundleRestrictIso (I * J) (hI.mul hJ) U).hom) W.1
      (((ModuleSheafTensor.tensor (divisorLineBundle I hI)
        (divisorLineBundle J hJ)).restrictAppIso U.ι W.1).inv
        (ModuleSheafTensor.pure (divisorLineBundle I hI) (divisorLineBundle J hJ)
          (U.ι ''ᵁ W) s t)) =
    moduleSectionApply ((divisorLineBundleSumRestrictSourceIso hI hJ U).hom ≫
        (divisorLineBundleSumOnIso hI hJ U).hom) W.1
      (((ModuleSheafTensor.tensor (divisorLineBundle I hI)
        (divisorLineBundle J hJ)).restrictAppIso U.ι W.1).inv
        (ModuleSheafTensor.pure (divisorLineBundle I hI) (divisorLineBundle J hJ)
          (U.ι ''ᵁ W) s t)) := by
  rw [divisorSumSection_comp (hI.comap_of_isOpenImmersion U.ι)
    (hJ.comap_of_isOpenImmersion U.ι) ((hI.mul hJ).comap_of_isOpenImmersion U.ι)
    (divisorLineBundleSumOnIso hI hJ U) (divisorLineBundleSumRestrictSourceIso hI hJ U).hom
    W _ _ _ (divisorLineBundleSumRestrictSourceIso_pure hI hJ U W.1 s t)]
  simp only [moduleSectionApply, Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply]
  rw [moduleRestrict_map_inv]
  exact divisorLineBundleSumRestrict_sections hI hJ U W hW hV s t

/-- Actual module-sheaf morphisms are determined on the common Cartier basis. -/
lemma moduleSectionApply_commonChart_ext {M N : X.Modules}
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) {f g : M ⟶ N}
    (h : ∀ (W : CommonCartierChart I J) (s : Γ(M, W.1.1)),
      moduleSectionApply f W.1.1 s = moduleSectionApply g W.1.1 s) : f = g := by
  apply (SheafOfModules.toSheaf X.ringCatSheaf).map_injective
  apply CategoryTheory.Sheaf.hom_ext
  apply (TopCat.Sheaf.restrictHomEquivHom _ _
    (commonCartierChart_isBasis hI hJ)).symm.injective
  ext W : 2
  apply ConcreteCategory.hom_ext
  exact h W.unop

/-- Restricting the global sum is the sum of the restricted divisors. -/
@[reassoc]
lemma divisorLineBundleSumRestrict (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).map (divisorLineBundleSumIso hI hJ).hom ≫
        (divisorLineBundleRestrictIso (I * J) (hI.mul hJ) U).hom =
      (divisorLineBundleSumRestrictSourceIso hI hJ U).hom ≫
        (divisorLineBundleSumOnIso hI hJ U).hom := by
  apply moduleSectionApply_commonChart_ext (hI.comap_of_isOpenImmersion U.ι)
    (hJ.comap_of_isOpenImmersion U.ι)
  intro W z
  let V := W.1
  have hW := (cartierChart_comap_iff I U.ι V).mp W.2.1
  have hV := (cartierChart_comap_iff J U.ι V).mp W.2.2
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ)).restrictAppIso
      U.ι V.1).inv).surjective z
  obtain ⟨z, rfl⟩ := (hW.tensorSectionsEquiv hV hI hJ).surjective z
  induction z using TensorProduct.inductionOn with
  | tmul s t => exact divisorLineBundleSumRestrict_pure hI hJ U V hW hV s t
  | add z w hz hw =>
    rw [(hW.tensorSectionsEquiv hV hI hJ).map_add z w]
    simp only [map_add, moduleSectionApply_add, hz, hw]

end FLT.Mazur.FCurve
