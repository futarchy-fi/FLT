/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundleSum
public import FLT.Mazur.RelativeSums

/-!
# Chart transport for open restriction of divisor sums

Product evaluation survives transport along open immersions. The actual tensor
restriction gives the source comparison, and pullback of the product ideal gives
the target comparison. The global and nested-open diagrams remain separate.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve

variable {X Y : Scheme.{u}} {I J : X.IdealSheafData}

/-- Transport preserves the product-evaluation formula of the chart sum. -/
lemma divisorChartTransport_sum_eval (f : Y ⟶ X) [IsOpenImmersion f]
    (W : Y.affineOpens)
    (hI : CartierChart I ⟨f ''ᵁ W, W.2.image_of_isOpenImmersion f⟩)
    (hJ : CartierChart J ⟨f ''ᵁ W, W.2.image_of_isOpenImmersion f⟩)
    (s : divisorChartModule I ⟨f ''ᵁ W, W.2.image_of_isOpenImmersion f⟩)
    (t : divisorChartModule J ⟨f ''ᵁ W, W.2.image_of_isOpenImmersion f⟩)
    (x : I.ideal ⟨f ''ᵁ W, W.2.image_of_isOpenImmersion f⟩)
    (y : J.ideal ⟨f ''ᵁ W, W.2.image_of_isOpenImmersion f⟩) :
    divisorChartTransport (I * J) f W (hI.sumEquiv hJ (s ⊗ₜ t))
      (CartierModule.idealRestrict _ _ _ (ideal_map_appIso (I * J) f W).le
        ⟨(x : Γ(X, f ''ᵁ W)) * y, Ideal.mul_mem_mul x.property y.property⟩) =
      divisorChartTransport I f W s
        (CartierModule.idealRestrict _ _ _ (ideal_map_appIso I f W).le x) *
      divisorChartTransport J f W t
        (CartierModule.idealRestrict _ _ _ (ideal_map_appIso J f W).le y) := by
  rw [divisorChartTransport_apply, CartierChart.sumEquiv_apply, map_mul,
    divisorChartTransport_apply, divisorChartTransport_apply]

/-- Equal ideal sheaves have canonically identical divisor line bundles. -/
def divisorLineBundleCongr {K L : X.IdealSheafData} (e : K = L)
    (hK : EffectiveCartier K) (hL : EffectiveCartier L) :
    divisorLineBundle K hK ≅ divisorLineBundle L hL :=
  eqToIso (by cases e; rfl)

/-- The sum of restricted divisors, with the product ideal identified canonically. -/
def divisorLineBundleSumOnIso (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (U : X.Opens) :
    ModuleSheafTensor.tensor (divisorLineBundleOn I hI U) (divisorLineBundleOn J hJ U) ≅
      divisorLineBundleOn (I * J) (hI.mul hJ) U :=
  divisorLineBundleSumIso (hI.comap_of_isOpenImmersion U.ι)
      (hJ.comap_of_isOpenImmersion U.ι) ≪≫
    divisorLineBundleCongr (idealSheaf_comap_mul I J U.ι).symm _ _

/-- The chart equivalence evaluates by the canonical pairing. -/
lemma CartierChart.divisorSectionsEquiv_eq_chartEval {W : X.affineOpens}
    (hW : CartierChart I W) (hI : EffectiveCartier I)
    (s : Γ(divisorLineBundle I hI, W.1)) :
    hW.divisorSectionsEquiv hI s = divisorChartEval I W s := rfl

/-- Identifying the product ideal preserves the sum's product evaluation. -/
lemma divisorLineBundleSumCongr_eval {K : X.IdealSheafData}
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) (hK : EffectiveCartier K)
    (e : I * J = K) (W : X.affineOpens)
    (hW : CartierChart I W) (hV : CartierChart J W) (hZ : CartierChart K W)
    (s : Γ(divisorLineBundle I hI, W.1)) (t : Γ(divisorLineBundle J hJ, W.1))
    (x : I.ideal W) (y : J.ideal W) (z : K.ideal W)
    (hxy : (x : Γ(X, W)) * y = z) :
    hZ.divisorSectionsEquiv hK
      (((divisorLineBundleSumIso hI hJ) ≪≫ divisorLineBundleCongr e (hI.mul hJ) hK).hom.app
        W.1 (ModuleSheafTensor.pure (divisorLineBundle I hI) (divisorLineBundle J hJ)
          W.1 s t)) z = hW.divisorSectionsEquiv hI s x * hV.divisorSectionsEquiv hJ t y := by
  cases e
  have hz : z = ⟨(x : Γ(X, W)) * y, Ideal.mul_mem_mul x.property y.property⟩ :=
    Subtype.ext hxy.symm
  subst z
  simpa only [divisorLineBundleCongr, eqToIso_refl, Iso.trans_refl,
    CartierChart.divisorSectionsEquiv_eq_chartEval] using
    divisorLineBundleSumIso_eval hI hJ W hW hV s t x y

/-- The source comparison uses tensor restriction and the two divisor comparisons. -/
def divisorLineBundleSumRestrictSourceIso (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) (U : X.Opens) :
    (ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ)).restrict
        U.ι ≅
      ModuleSheafTensor.tensor (divisorLineBundleOn I hI U) (divisorLineBundleOn J hJ U) :=
  ModuleSheafTensor.restrictIso _ _ U.ι ≪≫ ModuleSheafTensor.congr
    (divisorLineBundleRestrictIso I hI U) (divisorLineBundleRestrictIso J hJ U)

/-- The source comparison on pure sections. -/
lemma divisorLineBundleSumRestrictSourceIso_pure (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) (U : X.Opens) (W : U.toScheme.Opens)
    (s : Γ(divisorLineBundle I hI, U.ι ''ᵁ W))
    (t : Γ(divisorLineBundle J hJ, U.ι ''ᵁ W)) :
    (divisorLineBundleSumRestrictSourceIso hI hJ U).hom.app W
      (((ModuleSheafTensor.tensor (divisorLineBundle I hI)
        (divisorLineBundle J hJ)).restrictAppIso U.ι W).inv
        (ModuleSheafTensor.pure (divisorLineBundle I hI) (divisorLineBundle J hJ)
          (U.ι ''ᵁ W) s t)) =
      ModuleSheafTensor.pure (divisorLineBundleOn I hI U) (divisorLineBundleOn J hJ U) W
        ((divisorLineBundleRestrictIso I hI U).hom.app W
          (((divisorLineBundle I hI).restrictAppIso U.ι W).inv s))
        ((divisorLineBundleRestrictIso J hJ U).hom.app W
          (((divisorLineBundle J hJ).restrictAppIso U.ι W).inv t)) := by
  exact (congrArg ((ModuleSheafTensor.map (divisorLineBundleRestrictIso I hI U).hom
    (divisorLineBundleRestrictIso J hJ U).hom).app W)
    (ModuleSheafTensor.restrictIso_hom_pure (divisorLineBundle I hI)
      (divisorLineBundle J hJ) U.ι W s t)).trans
    (ModuleSheafTensor.map_pure (divisorLineBundleRestrictIso I hI U).hom
      (divisorLineBundleRestrictIso J hJ U).hom W
      (((divisorLineBundle I hI).restrictAppIso U.ι W).inv s)
      (((divisorLineBundle J hJ).restrictAppIso U.ι W).inv t))

/-- Products of ideal sections determine a dual section on a common Cartier chart. -/
lemma CartierChart.dual_ext_products {V : X.affineOpens}
    (hI : CartierChart I V) (hJ : CartierChart J V)
    {s t : divisorChartModule (I * J) V}
    (h : ∀ (x : I.ideal V) (y : J.ideal V),
      s ⟨(x : Γ(X, V)) * y, Ideal.mul_mem_mul x.property y.property⟩ =
        t ⟨(x : Γ(X, V)) * y, Ideal.mul_mem_mul x.property y.property⟩) : s = t := by
  ext z
  obtain ⟨r, hr⟩ := (CartierModule.idealEquiv _ _
    (hI.choose_spec.1.mul hJ.choose_spec.1)
    (by change I.ideal V * J.ideal V = _
        exact (congrArg₂ (· * ·) hI.choose_spec.2 hJ.choose_spec.2).trans
          (Ideal.span_singleton_mul_span_singleton _ _))).surjective z
  have hz : z = ⟨(hI.idealEquiv r : Γ(X, V)) * hJ.idealEquiv 1,
      Ideal.mul_mem_mul (hI.idealEquiv r).property (hJ.idealEquiv 1).property⟩ := by
    rw [← hr]
    apply Subtype.ext
    simp [CartierChart.idealEquiv, mul_assoc]
  rw [hz]
  exact h _ _

/-- Transported products still detect equality of dual sections. -/
lemma divisorChartTransport_dual_ext_products (f : Y ⟶ X) [IsOpenImmersion f]
    (W : Y.affineOpens)
    (hI : CartierChart I ⟨f ''ᵁ W, W.2.image_of_isOpenImmersion f⟩)
    (hJ : CartierChart J ⟨f ''ᵁ W, W.2.image_of_isOpenImmersion f⟩)
    {s t : divisorChartModule ((I * J).comap f) W}
    (h : ∀ (x : I.ideal ⟨f ''ᵁ W, W.2.image_of_isOpenImmersion f⟩)
      (y : J.ideal ⟨f ''ᵁ W, W.2.image_of_isOpenImmersion f⟩),
      s (CartierModule.idealRestrict _ _ _ (ideal_map_appIso (I * J) f W).le
        ⟨(x : Γ(X, f ''ᵁ W)) * y, Ideal.mul_mem_mul x.property y.property⟩) =
      t (CartierModule.idealRestrict _ _ _ (ideal_map_appIso (I * J) f W).le
        ⟨(x : Γ(X, f ''ᵁ W)) * y, Ideal.mul_mem_mul x.property y.property⟩)) : s = t := by
  apply (divisorChartTransport (I * J) f W).symm.injective
  apply hI.dual_ext_products hJ
  intro x y
  apply (f.appIso W).commRingCatIsoToRingEquiv.injective
  change (f.appIso W).hom.hom ((divisorChartTransport (I * J) f W).symm s _) =
    (f.appIso W).hom.hom ((divisorChartTransport (I * J) f W).symm t _)
  rw [← divisorChartTransport_apply (I * J) f W
    ((divisorChartTransport (I * J) f W).symm s),
    ← divisorChartTransport_apply (I * J) f W
      ((divisorChartTransport (I * J) f W).symm t),
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact h x y

/-- Restricting a morphism respects the canonical section identifications. -/
lemma moduleRestrict_map_inv {M N : X.Modules} (a : M ⟶ N)
    (f : Y ⟶ X) [IsOpenImmersion f] (W : Y.Opens) (s : Γ(M, f ''ᵁ W)) :
    ((Scheme.Modules.restrictFunctor f).map a).app W
        ((M.restrictAppIso f W).inv s) =
      (N.restrictAppIso f W).inv (a.app (f ''ᵁ W) s) := rfl

/-- Chart transport with the section identification made explicit. -/
lemma divisorLineBundleRestrictIso_chartTransport_inv (hI : EffectiveCartier I)
    (U : X.Opens) (W : U.toScheme.affineOpens)
    (hW : CartierChart I ⟨U.ι ''ᵁ W, W.2.image_of_isOpenImmersion U.ι⟩)
    (hV : CartierChart (I.comap U.ι) W)
    (s : Γ(divisorLineBundle I hI, U.ι ''ᵁ W)) :
    hV.divisorSectionsEquiv (hI.comap_of_isOpenImmersion U.ι)
        ((divisorLineBundleRestrictIso I hI U).hom.app W.1
          (((divisorLineBundle I hI).restrictAppIso U.ι W.1).inv s)) =
      divisorChartTransport I U.ι W (hW.divisorSectionsEquiv hI s) := by
  rw [CartierChart.divisorSectionsEquiv_eq_chartEval hV,
    CartierChart.divisorSectionsEquiv_eq_chartEval hW]
  exact divisorLineBundleRestrictIso_chartTransport I hI U W _

/-- Nested-open comparison is natural for any module-sheaf morphism. -/
@[reassoc]
lemma moduleRestrictLEIso_naturality {M N : X.Modules} (a : M ⟶ N)
    {U V : X.Opens} (h : V ≤ U) :
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
        ((Scheme.Modules.restrictFunctor U.ι).map a) ≫
      (moduleRestrictLEIso N h).hom =
    (moduleRestrictLEIso M h).hom ≫ (Scheme.Modules.restrictFunctor V.ι).map a := by
  have hn := (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).inv.naturality a
  simp only [Functor.comp_map] at hn
  simp only [moduleRestrictLEIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom]
  rw [← Category.assoc, hn, Category.assoc,
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).hom.naturality a]
  rfl

end FLT.Mazur.FCurve
