/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSmoothOrbitRecovery

/-!
# The original smooth orbit inside the actual model smooth locus

Lift the independently retained original smooth scheme, including its original
zero section, through the actual relative smooth-open inclusion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "V" => W.map (algebraMap R S)
local notation "g" => coefficientShearGluedStructure hπ data S r j hj
local notation "B" => coefficientShearSmoothEmbedding hπ data S r j hj
variable [LocallyOfFinitePresentation
  (coefficientShearGluedStructure hπ data S r j hj)]

/-- Every point of the independently retained orbit is smooth in the actual full model. -/
theorem coefficientShearSmoothEmbedding_range_smooth : Set.range B ⊆ (g).smoothLocus := by
  let _ : Smooth (B ≫ g) := by
    rw [coefficientShearSmoothEmbedding_structure]
    infer_instance
  have h := Scheme.Hom.preimage_smoothLocus_eq B g
  rw [Scheme.Hom.smoothLocus_eq_top (B ≫ g)] at h
  rintro _ ⟨x, rfl⟩
  exact h.ge (Set.mem_univ x)

/-- The full original smooth orbit as an open subscheme of the actual model smooth locus. -/
def coefficientShearSmoothOrbitToSmooth :
    (integralSmoothOpen V).toScheme ⟶ (g).smoothLocus.toScheme :=
  IsOpenImmersion.lift (g).smoothLocus.ι B (by
    rw [Scheme.Opens.range_ι]
    exact coefficientShearSmoothEmbedding_range_smooth hπ data S r j hj)

/-- Inclusion retains exactly the independently constructed original smooth embedding. -/
@[reassoc] theorem coefficientShearSmoothOrbitToSmooth_inclusion :
    coefficientShearSmoothOrbitToSmooth hπ data S r j hj ≫ (g).smoothLocus.ι = B :=
  IsOpenImmersion.lift_fac _ _ _

/-- The original zero section, now lying in the full actual model smooth locus. -/
def coefficientShearOriginalSmoothZero : Spec (.of S) ⟶ (g).smoothLocus.toScheme :=
  integralSmoothZero V ≫ coefficientShearSmoothOrbitToSmooth hπ data S r j hj

/-- Its inclusion is still the retained original zero, without choosing polygon coordinates. -/
@[reassoc] theorem coefficientShearOriginalSmoothZero_inclusion :
    coefficientShearOriginalSmoothZero hπ data S r j hj ≫ (g).smoothLocus.ι =
      integralSmoothZero V ≫ B := by
  rw [coefficientShearOriginalSmoothZero, Category.assoc,
    coefficientShearSmoothOrbitToSmooth_inclusion]

end FLT.Mazur.WeierstrassDividedDepth
