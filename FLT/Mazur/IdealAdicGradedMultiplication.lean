/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealPowerMultiplication
public import FLT.Mazur.ModuleTensorCokernelDescent

/-!
# Multiplication on the actual associated-graded ideal coefficients

Both next-power relations vanish under multiplication into the sum-degree
quotient. Bilinear descent therefore constructs multiplication on the actual
cokernels, retaining its value on the original ideal-power representatives.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.CoherentIdealIntersection
open ModuleSheafTensor

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)

/-- Multiplication into the sum-degree quotient kills the next left power. -/
lemma idealPowerMul_quotient_left (a b : ℕ) :
    ModuleSheafTensor.map (idealStep I a) (𝟙 _) ≫
      (idealPowerMul I a b ≫ cokernel.π (idealStep I (a + b))) = 0 := by
  rw [idealPowerMul_step_left_assoc, idealPowerStepAt_quotient, comp_zero]

/-- Multiplication into the sum-degree quotient kills the next right power. -/
lemma idealPowerMul_quotient_right (a b : ℕ) :
    ModuleSheafTensor.map (𝟙 _) (idealStep I b) ≫
      (idealPowerMul I a b ≫ cokernel.π (idealStep I (a + b))) = 0 := by
  rw [idealPowerMul_step_right_assoc, idealPowerStepAt_quotient, comp_zero]

/-- Multiplication on the actual ideal-power cokernels, adding their degrees. -/
def idealGradedMul (a b : ℕ) :
    tensor (idealGraded I a) (idealGraded I b) ⟶ idealGraded I (a + b) :=
  cokernelDesc (idealStep I a) (idealStep I b)
    (idealPowerMul I a b ≫ cokernel.π (idealStep I (a + b)))
    (idealPowerMul_quotient_left I a b) (idealPowerMul_quotient_right I a b)

/-- The graded multiplication is induced by the original ideal multiplication. -/
@[reassoc (attr := simp)]
lemma idealGradedMul_projection (a b : ℕ) :
    ModuleSheafTensor.map (cokernel.π (idealStep I a)) (cokernel.π (idealStep I b)) ≫
      idealGradedMul I a b = idealPowerMul I a b ≫ cokernel.π (idealStep I (a + b)) :=
  cokernelDesc_projection _ _ _ _ _

/-- Its value on representatives is the product followed by the actual quotient. -/
lemma idealGradedMul_pure (a b : ℕ) (U : X.Opens)
    (s : Γ(idealModule (I ^ a), U)) (t : Γ(idealModule (I ^ b), U)) :
    (idealGradedMul I a b).app U
      (pure _ _ U ((cokernel.π (idealStep I a)).app U s)
        ((cokernel.π (idealStep I b)).app U t)) =
      (cokernel.π (idealStep I (a + b))).app U
        ((idealPowerMul I a b).app U (pure _ _ U s t)) := by
  have h := congrArg (fun f ↦ f.app U (pure _ _ U s t)) (idealGradedMul_projection I a b)
  simpa only [idealGraded, Hom.comp_app, ConcreteCategory.comp_apply, map_pure] using h

omit [IsLocallyNoetherian X] in
/-- The quotient projections determine any bilinear morphism on graded pieces. -/
lemma idealGraded_tensor_hom_ext (a b : ℕ) {P : X.Modules}
    {f g : tensor (idealGraded I a) (idealGraded I b) ⟶ P}
    (h : ModuleSheafTensor.map (cokernel.π (idealStep I a))
      (cokernel.π (idealStep I b)) ≫ f =
        ModuleSheafTensor.map (cokernel.π (idealStep I a))
          (cokernel.π (idealStep I b)) ≫ g) : f = g := by
  have he : ModuleSheafTensor.map (cokernel.π (idealStep I a))
      (cokernel.π (idealStep I b)) =
        ModuleSheafTensor.map (cokernel.π (idealStep I a)) (𝟙 _) ≫
          ModuleSheafTensor.map (𝟙 _) (cokernel.π (idealStep I b)) := by
    rw [← map_comp]; simp
  rw [he, Category.assoc, Category.assoc] at h
  exact (cancel_epi (ModuleSheafTensor.map (𝟙 _) (cokernel.π (idealStep I b)))).mp
    ((cancel_epi (ModuleSheafTensor.map (cokernel.π (idealStep I a)) (𝟙 _))).mp h)

end FLT.Mazur.IdealAdicQuotient
