/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonClosedCyclicParameter
public import FLT.Mazur.PowerSeriesSmoothPointLift

/-!
# Lifting the prescribed labels into the complete one-gon smooth group

Smoothness constructs actual sections over the original complete base, one
for every prescribed closed label. Their multiplication defects reduce to the
identity. Correcting these defects to obtain a full cyclic marking is separate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ)
variable (labels : Multiplicative (ZMod n) →*
  (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
local notation "t" => (PowerSeries.X : PowerSeries K)
local notation "c" => Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))
local notation "G" => relativeGroup (t)

/-- Closed restriction as an actual relative arrow to the complete-base terminal object. -/
def completeClosedTestMap : Over.mk (c) ⟶ 𝟙_ (Over (Spec (.of (PowerSeries K)))) :=
  Over.homMk (c) (by simp)

/-- Every prescribed closed group label has a section over the same complete base. -/
theorem exists_completeLabelLift (a : Multiplicative (ZMod n)) :
    ∃ s : 𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶ (G).X,
      completeClosedTestMap K ≫ s = closedCyclicMarking K n labels a := by
  let _ : Smooth (G).X.hom :=
    WeierstrassIntegralChart.integralSmoothStructure_smooth (equation (t))
  obtain ⟨s, hs, hf⟩ := PowerSeriesSmoothPointLift.exists_lift (G).X.hom
    (closedCyclicMarking K n labels a).left (closedCyclicMarking K n labels a).w
  exact ⟨Over.homMk s hf, Over.OverMorphism.ext hs⟩

/-- The chosen whole-base lift of each prescribed closed label. -/
def completeLabelLift (a : Multiplicative (ZMod n)) :
    𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶ (G).X :=
  (exists_completeLabelLift K n labels a).choose

/-- Closed reduction retains each full original labeled scheme map. -/
@[reassoc] theorem completeLabelLift_reduction (a : Multiplicative (ZMod n)) :
    completeClosedTestMap K ≫ completeLabelLift K n labels a =
      closedCyclicMarking K n labels a :=
  (exists_completeLabelLift K n labels a).choose_spec

/-- Closed reduction is a homomorphism on all complete-base smooth-group sections. -/
def completeSectionReduction :
    (𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶ (G).X) →* (Over.mk (c) ⟶ (G).X) where
  toFun p := completeClosedTestMap K ≫ p
  map_one' := comp_one _
  map_mul' := comp_mul _

/-- The failure of arbitrary lifted labels to multiply correctly lies in the reduction kernel. -/
theorem completeLabelLift_multiplication_defect (a b : Multiplicative (ZMod n)) :
    completeSectionReduction K (completeLabelLift K n labels a * completeLabelLift K n labels b /
      completeLabelLift K n labels (a * b)) = 1 := by
  rw [map_div, map_mul]
  change (completeClosedTestMap K ≫ _) * (completeClosedTestMap K ≫ _) /
    (completeClosedTestMap K ≫ _) = 1
  rw [completeLabelLift_reduction, completeLabelLift_reduction, completeLabelLift_reduction,
    map_mul, div_self']

/-- The original closed label homomorphism detects faithfulness of any chosen complete lifts. -/
theorem completeLabelLift_injective (h : Function.Injective labels) :
    Function.Injective (completeLabelLift K n labels) := by
  intro a b hab
  apply closedCyclicMarking_injective K n labels h
  have he := congrArg (fun p ↦ completeClosedTestMap K ≫ p) hab
  simpa only [completeLabelLift_reduction] using he

end FLT.Mazur.OneGonSmoothing
