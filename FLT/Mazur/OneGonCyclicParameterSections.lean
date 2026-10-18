/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonFaithfulCompleteCyclicLift
public import FLT.Mazur.OneGonSmoothingCyclicIdeal

/-!
# Original sections of the lifted cyclic parameter

Projection of the parameter's relative sections recovers the constructed
complete marking. On the original closed fiber it recovers the given torus
labels as full scheme morphisms, rather than only as pointwise equalities.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  (labels : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hlabels : Function.Injective labels)
local notation "t" => (PowerSeries.X : PowerSeries K)
local notation "c" => Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))
local notation "G" => relativeGroup (t)
local notation "L" => Multiplicative (ZMod n)

/-- Evaluation of the complete parameter is exactly the constructed complete label. -/
@[reassoc] theorem faithfulCompleteParameter_value (a : L) :
    faithfulCompleteParameter K n labels hlabels ≫ faithfulInclusion (G).X L ≫
      value (G).X L a = faithfulCompleteMarking K n labels hlabels a := by
  rw [← Category.assoc, faithfulCompleteParameter_inclusion, liftMarking_value]

/-- The identity-base-change section projects to its actual complete label. -/
@[reassoc] theorem faithfulCompleteSections_fst (a : L) :
    (relativeCyclicMarking (t) n (𝟙 _) (faithfulCompleteParameter K n labels hlabels) a).left ≫
      pullback.fst (G).X.hom (𝟙 _) =
        (faithfulCompleteMarking K n labels hlabels a).left := by
  exact (faithfulSectionMarking_fst (G).X L (𝟙 _)
    (faithfulCompleteParameter K n labels hlabels) a).trans
      (congrArg Over.Hom.left (faithfulCompleteParameter_value K n labels hlabels a))

/-- The closed parameter gives precisely the originally prescribed closed smooth sections. -/
theorem closedCyclicParameter_sections (a : L) :
    relativeCyclicMarking (t) n (c) (closedCyclicParameter K n labels hlabels) a =
      closedCyclicSections K n labels a := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (faithfulSectionMarking_fst (G).X L (c)
      (closedCyclicParameter K n labels hlabels) a).trans ((congrArg Over.Hom.left
      (closedCyclicParameter_value K n labels hlabels a)).trans
        (closedCyclicMarking_left K n labels a))
  · exact (relativeCyclicMarking (t) n (c)
      (closedCyclicParameter K n labels hlabels) a).w.trans
        (closedCyclicSections K n labels a).w.symm

/-- The original torus comparison recovers every label of the closed parameter. -/
theorem closedCyclicParameter_sections_compare (a : L) :
    relativeCyclicMarking (t) n (c) (closedCyclicParameter K n labels hlabels) a ≫
      (completeClosedGroupTorusIso K).hom.hom.hom.hom = labels a := by
  rw [closedCyclicParameter_sections, closedCyclicSections_compare]

end FLT.Mazur.OneGonSmoothing
