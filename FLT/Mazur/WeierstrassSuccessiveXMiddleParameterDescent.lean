/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterPushout
public import FLT.Mazur.WeierstrassModificationXConicParameterNegation
public import FLT.Mazur.WeierstrassSuccessiveXMiddleScaledDescent

/-!
# Arbitrary-target descent from the original conic parameter and horizontal line

Descent retains the entire parameter open at nonzero constant. The opposite
node uses the original negated conic parameter with the same origin condition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] (c : K)
local notation "P" => Spec (CommRingCat.of (ConicParameterOpen c))
local notation "L" => Spec (CommRingCat.of (MiddleNodeOpen c))
local notation "o" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicParameterOrigin c)))
local notation "ν" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (AlgEquiv.toAlgHom (conicParameterNeg c))))

/-- Negation preserves the actual scheme-theoretic parameter origin. -/
@[reassoc] theorem middleParameterNeg_origin : o ≫ ν = o := by
  rw [← Spec.map_comp]
  exact congrArg (fun f : ConicParameterOpen c →ₐ[K] K =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (conicParameterNeg_origin c)

/-- Compatible maps from the original branches descend to the whole node. -/
def middleParameterDesc {Y : Scheme.{u}} (f : P ⟶ Y) (g : ProjectiveLine.chart K ⟶ Y)
    (w : o ≫ f = ProjectiveLine.chartZero K ≫ g) : L ⟶ Y :=
  (middleParameterBranches_isPushout c).desc f g w

/-- Descent recovers every function on the entire conic parameter open. -/
@[reassoc] theorem middleParameterConicBranch_desc {Y : Scheme.{u}}
    (f : P ⟶ Y) (g : ProjectiveLine.chart K ⟶ Y)
    (w : o ≫ f = ProjectiveLine.chartZero K ≫ g) :
    middleParameterConicBranch c ≫ middleParameterDesc c f g w = f :=
  (middleParameterBranches_isPushout c).inl_desc f g w

/-- Descent recovers the entire horizontal line. -/
@[reassoc] theorem middleParameterLineBranch_desc {Y : Scheme.{u}}
    (f : P ⟶ Y) (g : ProjectiveLine.chart K ⟶ Y)
    (w : o ≫ f = ProjectiveLine.chartZero K ≫ g) :
    middleParameterLineBranch c ≫ middleParameterDesc c f g w = g :=
  (middleParameterBranches_isPushout c).inr_desc f g w

/-- The two original complete restrictions determine every map out of the node. -/
theorem middleParameter_hom_ext {Y : Scheme.{u}} (f g : L ⟶ Y)
    (h₁ : middleParameterConicBranch c ≫ f = middleParameterConicBranch c ≫ g)
    (h₂ : middleParameterLineBranch c ≫ f = middleParameterLineBranch c ≫ g) : f = g :=
  (middleParameterBranches_isPushout c).hom_ext h₁ h₂

/-- Horizontal unit scaling retains the whole original parameter-open descent. -/
theorem middleParameter_exists_unique_scaled_desc (a : Kˣ) {Y : Scheme.{u}}
    (f : P ⟶ Y) (g : ProjectiveLine.chart K ⟶ Y)
    (w : o ≫ f = ProjectiveLine.chartZero K ≫ g) :
    ∃! d : L ⟶ Y, middleParameterConicBranch c ≫ d = f ∧
      ProjectiveLine.chartScaling K a ≫ middleParameterLineBranch c ≫ d = g := by
  let g' := ProjectiveLine.chartScaling K a⁻¹ ≫ g
  have w' : o ≫ f = ProjectiveLine.chartZero K ≫ g' := by
    simpa only [g', ProjectiveLine.chartZero_chartScaling_assoc] using w
  let d := middleParameterDesc c f g' w'
  have hf : middleParameterConicBranch c ≫ d = f :=
    middleParameterConicBranch_desc c f g' w'
  have hg : ProjectiveLine.chartScaling K a ≫ middleParameterLineBranch c ≫ d = g := by
    rw [middleParameterLineBranch_desc]
    simp only [g', ← Category.assoc, ← ProjectiveLine.chartScaling_mul,
      mul_inv_cancel, ProjectiveLine.chartScaling_one, Category.id_comp]
  refine ⟨d, ⟨hf, hg⟩, ?_⟩
  intro e he
  apply middleParameter_hom_ext c
  · exact he.1.trans hf.symm
  · exact middleNode_cancel_chartScaling a _ _ (he.2.trans hg.symm)

/-- The opposite chart descends with its original parameter negation. -/
theorem middleParameter_exists_unique_opposite_desc {Y : Scheme.{u}}
    (f : P ⟶ Y) (g : ProjectiveLine.chart K ⟶ Y)
    (w : o ≫ f = ProjectiveLine.chartZero K ≫ g) :
    ∃! d : L ⟶ Y, middleParameterConicBranch c ≫ d = ν ≫ f ∧
      middleParameterLineBranch c ≫ d = g := by
  have w' : o ≫ ν ≫ f = ProjectiveLine.chartZero K ≫ g := by
    rw [middleParameterNeg_origin_assoc]
    exact w
  refine ⟨middleParameterDesc c (ν ≫ f) g w',
    ⟨middleParameterConicBranch_desc c _ _ _, middleParameterLineBranch_desc c _ _ _⟩, ?_⟩
  intro e he
  apply middleParameter_hom_ext c
  · rw [he.1, middleParameterConicBranch_desc]
  · rw [he.2, middleParameterLineBranch_desc]

end FLT.Mazur.WeierstrassSuccessiveX
