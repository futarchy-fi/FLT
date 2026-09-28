/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundleSum

/-!
# Empty-divisor coherence for the divisor sum

The constructed sum comparison agrees with the tensor unit comparisons.
The proof evaluates on products with the element one of the unit ideal.
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

/-- Equality of ideals identifies their positive divisor sheaves. -/
def divisorLineBundleEqIso (h : I = J) (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) : divisorLineBundle I hI ≅ divisorLineBundle J hJ :=
  eqToIso (by subst J; rfl)

/-- Transport along equality preserves evaluation on the corresponding ideal element. -/
lemma divisorLineBundleEqIso_eval (h : I = J) (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) (U : X.affineOpens)
    (s : Γ(divisorLineBundle I hI, U.1)) (x : I.ideal U) (y : J.ideal U)
    (hxy : (x : Γ(X, U)) = y) :
    divisorChartEval J U ((divisorLineBundleEqIso h hI hJ).hom.app U.1 s) y =
      divisorChartEval I U s x := by
  subst J
  have : x = y := Subtype.ext hxy
  subst y
  rfl

/-- Evaluation at one is the prescribed trivialization of the empty divisor. -/
lemma divisorLineBundleTopIso_eval (U : X.affineOpens)
    (s : Γ(divisorLineBundle (⊤ : X.IdealSheafData) effectiveCartier_top, U.1)) :
    (divisorLineBundleTopIso effectiveCartier_top).hom.app U.1 s =
      divisorChartEval ⊤ U s ⟨1, by simp⟩ := by
  change moduleDualEval (structureModule X) U.1
    ((Scheme.Modules.restrictFunctor U.1.ι).map idealModuleTopIso.inv ≫ s) (1 : Γ(X, U)) = _
  rw [moduleDualEval_precomp]
  change moduleDualEval (idealModule ⊤) U.1 s _ =
    moduleDualEval (idealModule ⊤) U.1 s _
  congr 1
  apply (idealModuleAffineEquiv ⊤ U).injective
  apply Subtype.ext
  erw [LinearEquiv.apply_symm_apply, idealModuleAffineEquiv_val]
  exact congrArg (fun f ↦ f.app U.1 (1 : Γ(X, U))) idealModuleTopIso.inv_hom_id

/-- It suffices to compare tensor maps on pure sections of common Cartier charts. -/
lemma divisorTensorHom_ext (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    {P : X.Modules}
    {f g : ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ) ⟶ P}
    (h : ∀ (U : X.affineOpens), CartierChart I U → CartierChart J U →
      ∀ s t, f.app U.1 (ModuleSheafTensor.pure _ _ U.1 s t) =
        g.app U.1 (ModuleSheafTensor.pure _ _ U.1 s t)) : f = g := by
  apply (SheafOfModules.toSheaf X.ringCatSheaf).map_injective
  apply CategoryTheory.Sheaf.hom_ext
  apply (TopCat.Sheaf.restrictHomEquivHom _ _ (commonCartierChart_isBasis hI hJ)).symm.injective
  ext U : 2
  apply ConcreteCategory.hom_ext
  intro z
  change f.app U.unop.1.1 z = g.app U.unop.1.1 z
  obtain ⟨z, rfl⟩ := (U.unop.2.1.tensorSectionsEquiv U.unop.2.2 hI hJ).surjective z
  induction z using TensorProduct.inductionOn with
  | tmul s t => exact h U.unop.1 U.unop.2.1 U.unop.2.2 s t
  | add z w hz hw =>
    rw [(U.unop.2.1.tensorSectionsEquiv U.unop.2.2 hI hJ).map_add]
    simp only [map_add, hz, hw]

/-- The canonical interchange of the factors of the constructed sheaf tensor. -/
def ModuleSheafTensor.swap (M N : X.Modules) : tensor M N ≅ tensor N M := by
  let f (M N : X.Modules) : tensor M N ⟶ tensor N M :=
    lift { app U := ((pairing N M).app U).flip
           naturality i m n := (pairing N M).naturality i n m }
  exact
    { hom := f M N
      inv := f N M
      hom_inv_id := by
        apply hom_ext
        intro U m n
        simp [f, LinearMap.flip_apply]
      inv_hom_id := by
        apply hom_ext
        intro U m n
        simp [f, LinearMap.flip_apply] }

@[simp]
lemma ModuleSheafTensor.swap_pure (M N : X.Modules) (U : X.Opens)
    (m : Γ(M, U)) (n : Γ(N, U)) :
    (swap M N).hom.app U (pure M N U m n) = pure N M U n m :=
  lift_pure _ U m n

/-- Addition of the empty divisor on the left is the prescribed left unit map. -/
theorem divisorLineBundleSumIso_leftUnit (hI : EffectiveCartier I) :
    divisorLineBundleSumIso effectiveCartier_top hI ≪≫
        divisorLineBundleEqIso (Scheme.IdealSheafData.top_mul I) _ hI =
      ModuleSheafTensor.congr (divisorLineBundleTopIso effectiveCartier_top) (Iso.refl _) ≪≫
        ModuleSheafTensor.leftUnitor (divisorLineBundle I hI) := by
  apply Iso.ext
  apply divisorTensorHom_ext effectiveCartier_top hI
  intro U hU hV s t
  apply hV.divisorChartEval_bijective.injective
  apply LinearMap.ext
  intro y
  have he := divisorLineBundleSumIso_eval effectiveCartier_top hI U hU hV s t
    ⟨1, by simp⟩ y
  rw [Iso.trans_hom, Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply,
    divisorLineBundleEqIso_eval _ _ _ U _
      ⟨1 * y, Ideal.mul_mem_mul (by simp) y.property⟩ y (by simp)]
  rw [he]
  simp only [Iso.trans_hom, Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply,
    ModuleSheafTensor.congr, ModuleSheafTensor.map_pure, Iso.refl_hom,
    Scheme.Modules.Hom.id_app, AddCommGrpCat.id_apply, divisorLineBundleTopIso_eval]
  erw [ModuleSheafTensor.leftUnitor_pure]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- Addition on the right uses the canonical factor swap and the left unit map. -/
theorem divisorLineBundleSumIso_rightUnit (hI : EffectiveCartier I) :
    divisorLineBundleSumIso hI effectiveCartier_top ≪≫
        divisorLineBundleEqIso (Scheme.IdealSheafData.mul_top I) _ hI =
      ModuleSheafTensor.swap (divisorLineBundle I hI)
          (divisorLineBundle ⊤ effectiveCartier_top) ≪≫
        ModuleSheafTensor.congr (divisorLineBundleTopIso effectiveCartier_top) (Iso.refl _) ≪≫
          ModuleSheafTensor.leftUnitor (divisorLineBundle I hI) := by
  apply Iso.ext
  apply divisorTensorHom_ext hI effectiveCartier_top
  intro U hU hV s t
  apply hU.divisorChartEval_bijective.injective
  apply LinearMap.ext
  intro x
  have he := divisorLineBundleSumIso_eval hI effectiveCartier_top U hU hV s t
    x ⟨1, by simp⟩
  rw [Iso.trans_hom, Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply,
    divisorLineBundleEqIso_eval _ _ _ U _
      ⟨(x : Γ(X, U)) * 1, Ideal.mul_mem_mul x.property (by simp)⟩ x (by simp)]
  rw [he]
  simp only [Iso.trans_hom, Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply,
    ModuleSheafTensor.swap_pure, ModuleSheafTensor.congr, ModuleSheafTensor.map_pure,
    Iso.refl_hom, Scheme.Modules.Hom.id_app, AddCommGrpCat.id_apply,
    divisorLineBundleTopIso_eval]
  erw [ModuleSheafTensor.leftUnitor_pure]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm]

end FLT.Mazur.FCurve
