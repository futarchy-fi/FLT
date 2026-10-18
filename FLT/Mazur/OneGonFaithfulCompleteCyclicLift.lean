/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteKernelPowers
public import FLT.Mazur.FaithfulTorusCyclicIndex

/-!
# Actual complete lifts of every faithful finite cyclic torus labeling

Faithfulness supplies the unit-index condition. Complete kernel divisibility
then constructs the whole cyclic marking and its original faithful parameter,
retaining the prescribed closed labeling without extra lifting assumptions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open AuxiliaryLevel

variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  (labels : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hlabels : Function.Injective labels)
local notation "G" => relativeGroup (PowerSeries.X : PowerSeries K)
local notation "L" => Multiplicative (ZMod n)

/-- The original faithful closed labels alone determine a complete cyclic marking. -/
def faithfulCompleteMarking : L →*
    (𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶ (G).X) :=
  unitIndexCompleteMarking K n labels
    (FaithfulTorusCyclicIndex.powerSeries_index_unit K n labels hlabels)

/-- The complete cyclic marking retains every full closed relative point. -/
@[reassoc] theorem faithfulCompleteMarking_reduction (a : L) :
    completeClosedTestMap K ≫ faithfulCompleteMarking K n labels hlabels a =
      closedCyclicMarking K n labels a := unitIndexCompleteMarking_reduction K n labels _ a

/-- The complete cyclic marking is faithful. -/
theorem faithfulCompleteMarking_injective :
    Function.Injective (faithfulCompleteMarking K n labels hlabels) :=
  unitIndexCompleteMarking_injective K n labels _ hlabels

/-- Every complete cyclic marking with these closed labels equals the constructed marking. -/
theorem faithfulCompleteMarking_unique
    (q : L →* (𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶ (G).X))
    (hq : (completeSectionReduction K).comp q = closedCyclicMarking K n labels) :
    q = faithfulCompleteMarking K n labels hlabels :=
  correctedCompleteMarking_unique K n labels _ q hq

/-- Every original faithful closed cyclic labeling lifts to the actual complete parameter scheme. -/
def faithfulCompleteParameter :
    𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶
      relativeCyclicParameter (PowerSeries.X : PowerSeries K) n :=
  correctedCompleteParameter K n labels (completeSectionReduction_kernel_pow_bijective K n
    (FaithfulTorusCyclicIndex.powerSeries_index_unit K n labels hlabels)) hlabels

/-- The complete faithful parameter classifies exactly the constructed whole cyclic marking. -/
@[reassoc] theorem faithfulCompleteParameter_inclusion :
    faithfulCompleteParameter K n labels hlabels ≫ faithfulInclusion (G).X L =
      liftMarking (G).X L (faithfulCompleteMarking K n labels hlabels) :=
  correctedCompleteParameter_inclusion K n labels _ hlabels

/-- The complete faithful parameter restricts to the original specified closed parameter. -/
@[reassoc] theorem faithfulCompleteParameter_reduction :
    completeClosedTestMap K ≫ faithfulCompleteParameter K n labels hlabels =
      closedCyclicParameter K n labels hlabels :=
  correctedCompleteParameter_reduction K n labels _ hlabels

/-- Lifting coverage for every faithful finite cyclic torus labeling over every field. -/
theorem exists_faithfulCompleteParameter :
    ∃ p : 𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶
        relativeCyclicParameter (PowerSeries.X : PowerSeries K) n,
      completeClosedTestMap K ≫ p = closedCyclicParameter K n labels hlabels :=
  ⟨faithfulCompleteParameter K n labels hlabels,
    faithfulCompleteParameter_reduction K n labels hlabels⟩

end FLT.Mazur.OneGonSmoothing
