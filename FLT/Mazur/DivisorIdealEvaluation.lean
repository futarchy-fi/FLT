/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorSectionExact
public import FLT.Mazur.ModuleSheafDualInternalHom
public import FLT.Mazur.ModuleSheafTensorAssociator
public import FLT.Mazur.ModuleSheafTensorAffineOpen

/-!
# Contraction of a Cartier ideal with its divisor line

The actual evaluation pairing is invertible, as checked on Cartier charts.
It identifies the tensor of the ideal inclusion with the canonical section map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleSheafTensorAssociator

variable {X : Scheme.{u}} {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- Contraction, with the ideal in the first tensor factor. -/
def divisorIdealEvaluation :
    tensor (idealModule I) (divisorLineBundle I hI) ⟶ structureModule X :=
  (comm _ _).hom ≫ moduleSheafDualEvaluation (idealModule I)

/-- The contraction is the intrinsic dual evaluation on pure sections. -/
lemma divisorIdealEvaluation_pure (U : X.Opens) (s : Γ(idealModule I, U))
    (φ : Γ(divisorLineBundle I hI, U)) :
    (divisorIdealEvaluation hI).app U (pure _ _ U s φ) =
      moduleDualEval (idealModule I) U φ s := by
  simp only [divisorIdealEvaluation, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, comm_hom_pure]
  exact moduleSheafDualEvaluation_pure _ U φ s

/-- Evaluation is bijective on every Cartier chart. -/
lemma CartierChart.divisorIdealEvaluation_bijective {U : X.affineOpens}
    (hU : CartierChart I U) : Function.Bijective ((divisorIdealEvaluation hI).app U.1) := by
  let M := idealModule I
  let N := divisorLineBundle I hI
  let c := hU.idealTrivialization
  let d := hU.divisorTrivialization hI
  have hc : (unit (M.restrict U.1.ι) (N.restrict U.1.ι)).app (op ⊤) =
      ModuleCat.ofHom (trivialSectionsEquiv c d ⊤).toLinearMap := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    exact (trivialSectionsEquiv_tmul c d ⊤ m n).symm
  have ht := unit_image_bijective M N U.1.ι ⊤
    (by rw [hc]; exact (trivialSectionsEquiv c d ⊤).bijective)
  rw [Scheme.Opens.ι_image_top] at ht
  let a := (idealModuleAffineEquiv I U).trans hU.idealEquiv.symm
  let b := (hU.divisorSectionsEquiv hI).trans hU.dualEquiv
  let t : Γ(idealModule I, U.1) ⊗[Γ(X, U)] Γ(divisorLineBundle I hI, U.1) ≃ₗ[Γ(X, U)]
      Γ(tensor (idealModule I) (divisorLineBundle I hI), U.1) :=
    LinearEquiv.ofBijective ((unit M N).app (op U.1)).hom ht
  let e := t.symm.trans ((TensorProduct.congr a b).trans (TensorProduct.lid _ _))
  have he : ∀ z, (divisorIdealEvaluation hI).app U.1 (t z) = e (t z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul s φ =>
      change (divisorIdealEvaluation hI).app U.1 (pure _ _ _ s φ) = _
      rw [divisorIdealEvaluation_pure]
      have heval : moduleDualEval (idealModule I) U.1 φ s =
          divisorChartEval I U φ (idealModuleAffineEquiv I U s) := by
        change _ = moduleDualEval (idealModule I) U.1 φ
          ((idealModuleAffineEquiv I U).symm (idealModuleAffineEquiv I U s))
        rw [LinearEquiv.symm_apply_apply]
      rw [heval]
      obtain ⟨r, hr⟩ := hU.idealEquiv.surjective (idealModuleAffineEquiv I U s)
      have hs : idealModuleAffineEquiv I U s = r • hU.idealEquiv 1 := by
        rw [← hr, ← map_smul]
        simp
      dsimp only [e, LinearEquiv.trans_apply]
      rw [LinearEquiv.symm_apply_apply]
      simp only [TensorProduct.congr_tmul, TensorProduct.lid_tmul, smul_eq_mul]
      rw [hs, map_smul]
      change r * hU.dualEquiv (divisorChartEval I U φ) = a s * b φ
      have ha : a s = r := by
        change hU.idealEquiv.symm (idealModuleAffineEquiv I U s) = r
        rw [← hr, LinearEquiv.symm_apply_apply]
      rw [ha]
      rfl
    | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  have hf : ∀ z, (divisorIdealEvaluation hI).app U.1 z = e z := by
    intro z
    obtain ⟨z, rfl⟩ := t.surjective z
    exact he z
  change Function.Bijective (fun z ↦ (divisorIdealEvaluation hI).app U.1 z)
  rw [funext hf]
  exact e.bijective

/-- The canonical contraction is a global isomorphism, without chosen global coordinates. -/
instance divisorIdealEvaluation_isIso : IsIso (divisorIdealEvaluation hI) := by
  let f := (SheafOfModules.toSheaf _).map (divisorIdealEvaluation hI)
  have hf : IsIso f := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (commonCartierChart_isBasis hI hI)
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    exact U.2.1.divisorIdealEvaluation_bijective hI
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  exact inferInstanceAs (IsIso (f.hom.app (op U)))

/-- The evaluation isomorphism trivializes the ideal tensored with its dual. -/
def divisorIdealEvaluationIso :
    tensor (idealModule I) (divisorLineBundle I hI) ≅ structureModule X :=
  asIso (divisorIdealEvaluation hI)

end FLT.Mazur.FCurve
