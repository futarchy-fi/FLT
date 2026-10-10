/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper

/-!
# The retained original zero on every finite projective model

The unchanged chart at infinity contains the original zero point. It gives
an actual section of the new proper structure map and remains that same
point under contraction and arbitrary scheme base change.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
open WeierstrassIntegralChart

/-- The original point at infinity as an actual point of the whole modified cubic. -/
def finiteGlobalZero : Spec (.of R) ⟶ finiteGlobalModel hπ data j hj :=
  Spec.map (CommRingCat.ofHom (chartInfinityEvaluation (S := R) W).toRingHom) ≫
    finiteInfinityChart hπ data j hj

/-- Contraction retains the exact original zero point. -/
@[reassoc] theorem finiteGlobalZero_contraction :
    finiteGlobalZero hπ data j hj ≫ finiteGlobalContraction hπ data j hj =
      integralCurveZero W := by
  rw [finiteGlobalZero, Category.assoc, finiteInfinityChart_contraction]
  rfl

/-- The retained zero point is an actual section over the whole coefficient scheme. -/
@[reassoc] theorem finiteGlobalZero_structure :
    finiteGlobalZero hπ data j hj ≫ finiteGlobalStructure hπ data j hj = 𝟙 _ := by
  rw [finiteGlobalStructure, finiteGlobalZero_contraction_assoc, integralCurveZero_structure]

/-- The whole finite projective model meets every fiber of the original base. -/
instance finiteGlobalStructure_surjective : Surjective (finiteGlobalStructure hπ data j hj) := by
  constructor
  intro x
  refine ⟨finiteGlobalZero hπ data j hj x, ?_⟩
  exact congrArg (fun f => f x) (finiteGlobalZero_structure hπ data j hj)

variable {S : Scheme.{u}} (f : S ⟶ Spec (.of R))

/-- Arbitrary base change retains the original infinity section. -/
def finiteGlobalBaseChangeZero : S ⟶ pullback (finiteGlobalStructure hπ data j hj) f :=
  pullback.lift (f ≫ finiteGlobalZero hπ data j hj) (𝟙 S) (by
    rw [Category.assoc, finiteGlobalZero_structure, Category.comp_id, Category.id_comp])

/-- The retained section remains a section after arbitrary base change. -/
@[reassoc] theorem finiteGlobalBaseChangeZero_structure :
    finiteGlobalBaseChangeZero hπ data j hj f ≫
      pullback.snd (finiteGlobalStructure hπ data j hj) f = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- Every scheme base change of the whole model is a closed surjection. -/
theorem finiteGlobalBaseChange_closedSurjective :
    IsClosedMap (pullback.snd (finiteGlobalStructure hπ data j hj) f) ∧
      Function.Surjective (pullback.snd (finiteGlobalStructure hπ data j hj) f) :=
  ⟨(pullback.snd (finiteGlobalStructure hπ data j hj) f).isClosedMap,
    (pullback.snd (finiteGlobalStructure hπ data j hj) f).surjective⟩

end FLT.Mazur.WeierstrassDividedDepth
