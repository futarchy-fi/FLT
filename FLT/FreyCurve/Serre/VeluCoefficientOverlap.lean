/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluCoefficientGaloisAction
public import FLT.Mazur.GaloisTensorCartesian

/-!
# Galois graphs in the original cubic coefficient overlap

The actual kernel pair maps to the coefficient tensor spectrum. Each Galois
graph is exactly the base change of its original coefficient evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart FLT.Mazur.GaloisTensorPrime
open scoped TensorProduct

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  (E : WeierstrassCurve K)

local notation "c" => integralCoefficientMorphism (S := L) E
local notation "s" => integralCurveStructure (E.map (algebraMap K L))

/-- The actual cubic kernel pair projects to the original coefficient overlap. -/
def coefficientOverlapBase : pullback c c ⟶ Spec (.of (L ⊗[K] L)) :=
  tensor_isPullback.lift (pullback.fst c c ≫ s) (pullback.snd c c ≫ s) (by
    simp only [Category.assoc, ← integralCoefficientMorphism_structure,
      pullback.condition_assoc])

/-- The first coefficient is the structure map of the original first source. -/
@[reassoc] theorem coefficientOverlapBase_fst :
    coefficientOverlapBase E ≫ tensorFst = pullback.fst c c ≫ s :=
  tensor_isPullback.lift_fst _ _ _

/-- The second coefficient is the structure map of the original second source. -/
@[reassoc] theorem coefficientOverlapBase_snd :
    coefficientOverlapBase E ≫ tensorSnd = pullback.snd c c ≫ s :=
  tensor_isPullback.lift_snd _ _ _

/-- The actual Galois graph inside the original cubic kernel pair. -/
def coefficientGaloisGraph (g : L ≃ₐ[K] L) :
    integralCurve (E.map (algebraMap K L)) ⟶ pullback c c :=
  pullback.lift (𝟙 _) (integralGaloisMap E g) (by
    rw [Category.id_comp, integralGaloisMap_coefficient])

/-- The graph keeps the first source unchanged. -/
@[reassoc] theorem coefficientGaloisGraph_fst (g : L ≃ₐ[K] L) :
    coefficientGaloisGraph E g ≫ pullback.fst c c = 𝟙 _ := pullback.lift_fst ..

/-- The graph has precisely the original Galois action as second projection. -/
@[reassoc] theorem coefficientGaloisGraph_snd (g : L ≃ₐ[K] L) :
    coefficientGaloisGraph E g ≫ pullback.snd c c = integralGaloisMap E g :=
  pullback.lift_snd ..

/-- The graph lies over its original coefficient evaluation. -/
@[reassoc] theorem coefficientGaloisGraph_base (g : L ≃ₐ[K] L) :
    coefficientGaloisGraph E g ≫ coefficientOverlapBase E = s ≫ evaluationSpec g := by
  apply tensor_isPullback.hom_ext
  · simp only [Category.assoc, coefficientOverlapBase_fst, coefficientGaloisGraph_fst_assoc,
      evaluationSpec_fst, Category.comp_id]
  · simp only [Category.assoc, coefficientOverlapBase_snd, coefficientGaloisGraph_snd_assoc,
      evaluationSpec_snd, integralGaloisMap_structure]

/-- Each actual Galois graph is the pullback of the corresponding tensor evaluation. -/
theorem coefficientGaloisGraph_isPullback (g : L ≃ₐ[K] L) :
    IsPullback (coefficientGaloisGraph E g) s (coefficientOverlapBase E) (evaluationSpec g) := by
  refine IsPullback.mk' (coefficientGaloisGraph_base E g) ?_ ?_
  · intro T a b h _
    have he := congrArg (fun f ↦ f ≫ pullback.fst c c) h
    simpa only [Category.assoc, coefficientGaloisGraph_fst, Category.comp_id] using he
  · intro T a b h
    have h₁ := congrArg (fun f ↦ f ≫ tensorFst) h
    have h₂ := congrArg (fun f ↦ f ≫ tensorSnd) h
    simp only [Category.assoc, coefficientOverlapBase_fst, evaluationSpec_fst,
      Category.comp_id] at h₁
    simp only [Category.assoc, coefficientOverlapBase_snd, evaluationSpec_snd] at h₂
    refine ⟨a ≫ pullback.fst c c, ?_, h₁⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, coefficientGaloisGraph_fst, Category.comp_id]
    · simp only [Category.assoc, coefficientGaloisGraph_snd]
      apply (integralCoefficient_isPullback E).hom_ext
      · simp only [Category.assoc, integralGaloisMap_coefficient, pullback.condition]
      · rw [Category.assoc, Category.assoc, integralGaloisMap_structure]
        simpa only [Category.assoc, ← h₁] using h₂.symm

end WeierstrassCurve.Velu
