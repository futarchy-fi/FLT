/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentCommonStage

/-!
# Refining independently descended smooth factors

An actual stage transition carries the smooth factor and its entire cubic
factorization to the common finite ring. Recovery follows from this equation,
so independent choices require no assumed recovered embedding equality.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonSmoothing WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s : Set R)
  {i k : (CoefficientStage (base I t ht n s))ᵒᵖ} (α : k ⟶ i)
  (b : (coefficientModelDiagram (base I t ht n s) (carrier I t ht n s).hom).obj i ⟶
    (integralSmoothOpen (equation (parameter I t ht n s))).toScheme)
  (hb : b ≫ (integralSmoothOpen (equation (parameter I t ht n s))).ι =
    (coefficientModelToInitial (base I t ht n s) (carrier I t ht n s).hom).app i ≫
      embedding I t ht n s)

/-- Refine the actual smooth map along the specified coefficient transition. -/
def refinedFactor :
    (coefficientModelDiagram (base I t ht n s) (carrier I t ht n s).hom).obj k ⟶
      (integralSmoothOpen (equation (parameter I t ht n s))).toScheme :=
  (coefficientModelDiagram (base I t ht n s) (carrier I t ht n s).hom).map α ≫ b

include hb in
/-- Refinement retains the whole-cubic factorization at its actual new stage. -/
@[reassoc] theorem refinedFactor_inclusion :
    refinedFactor I t ht n s α b ≫ (integralSmoothOpen (equation (parameter I t ht n s))).ι =
      (coefficientModelToInitial (base I t ht n s) (carrier I t ht n s).hom).app k ≫
        embedding I t ht n s := by
  rw [refinedFactor, Category.assoc, hb, ← Category.assoc]
  simp only [coefficientModelDiagram, schemeBaseChangeDiagram, coefficientModelToInitial,
    Limits.pullback.lift_fst, Category.comp_id]

include hb in
/-- Recovery of every refinement is the original canonical smooth factor. -/
@[reassoc] theorem refinedFactor_recovery :
    (coefficientModelCone (base I t ht n s) (carrier I t ht n s).hom).π.app k ≫
      refinedFactor I t ht n s α b = recoveredSmoothFactor I t ht n s :=
  stageFactor_recovery I t ht n s k (refinedFactor I t ht n s α b)
    (refinedFactor_inclusion I t ht n s α b hb)

include hb in
/-- Two smooth factorizations of the same full embedding agree at any shared refinement. -/
theorem refinedFactor_unique
    {j : (CoefficientStage (base I t ht n s))ᵒᵖ} (β : k ⟶ j)
    (c : (coefficientModelDiagram (base I t ht n s) (carrier I t ht n s).hom).obj j ⟶
      (integralSmoothOpen (equation (parameter I t ht n s))).toScheme)
    (hc : c ≫ (integralSmoothOpen (equation (parameter I t ht n s))).ι =
      (coefficientModelToInitial (base I t ht n s) (carrier I t ht n s).hom).app j ≫
        embedding I t ht n s) :
    refinedFactor I t ht n s α b = refinedFactor I t ht n s β c := by
  apply (cancel_mono (integralSmoothOpen (equation (parameter I t ht n s))).ι).mp
  rw [refinedFactor_inclusion I t ht n s α b hb,
    refinedFactor_inclusion I t ht n s β c hc]

variable (u : Set R) (j : (CoefficientStage (base I t ht n u))ᵒᵖ)
  (c : (coefficientModelDiagram (base I t ht n u) (carrier I t ht n u).hom).obj j ⟶
    (integralSmoothOpen (equation (parameter I t ht n u))).toScheme)
  (hc : c ≫ (integralSmoothOpen (equation (parameter I t ht n u))).ι =
    (coefficientModelToInitial (base I t ht n u) (carrier I t ht n u).hom).app j ≫
      embedding I t ht n u)

/-- The left smooth factor over the constructed common finite ring. -/
def commonFactorLeft :
    (coefficientModelDiagram (base I t ht n s) (carrier I t ht n s).hom).obj
      (commonLeft I t ht n s u i j) ⟶
        (integralSmoothOpen (equation (parameter I t ht n s))).toScheme :=
  refinedFactor I t ht n s (commonToLeft I t ht n s u i j) b

/-- The right smooth factor over precisely the same common finite ring. -/
def commonFactorRight :
    (coefficientModelDiagram (base I t ht n u) (carrier I t ht n u).hom).obj
      (commonRight I t ht n s u i j) ⟶
        (integralSmoothOpen (equation (parameter I t ht n u))).toScheme :=
  refinedFactor I t ht n u (commonToRight I t ht n s u i j) c

include hb hc in
/-- Both actual common-stage maps retain their independent whole-cubic factorizations. -/
theorem commonFactors_inclusion :
    (commonFactorLeft I t ht n s b u j ≫
        (integralSmoothOpen (equation (parameter I t ht n s))).ι =
      (coefficientModelToInitial (base I t ht n s) (carrier I t ht n s).hom).app
        (commonLeft I t ht n s u i j) ≫ embedding I t ht n s) ∧
    (commonFactorRight I t ht n s (i := i) u j c ≫
        (integralSmoothOpen (equation (parameter I t ht n u))).ι =
      (coefficientModelToInitial (base I t ht n u) (carrier I t ht n u).hom).app
        (commonRight I t ht n s u i j) ≫ embedding I t ht n u) :=
  ⟨refinedFactor_inclusion I t ht n s (commonToLeft I t ht n s u i j) b hb,
    refinedFactor_inclusion I t ht n u (commonToRight I t ht n s u i j) c hc⟩

include hb hc in
/-- Both independent maps recover the canonical smooth factors, with no recovery premises. -/
theorem commonFactors_recovery :
    (coefficientModelCone (base I t ht n s) (carrier I t ht n s).hom).π.app
        (commonLeft I t ht n s u i j) ≫ commonFactorLeft I t ht n s b u j =
      recoveredSmoothFactor I t ht n s ∧
    (coefficientModelCone (base I t ht n u) (carrier I t ht n u).hom).π.app
        (commonRight I t ht n s u i j) ≫ commonFactorRight I t ht n s (i := i) u j c =
      recoveredSmoothFactor I t ht n u :=
  ⟨refinedFactor_recovery I t ht n s (commonToLeft I t ht n s u i j) b hb,
    refinedFactor_recovery I t ht n u (commonToRight I t ht n s u i j) c hc⟩

end FLT.Mazur.OneGonAdicIndependentModel
