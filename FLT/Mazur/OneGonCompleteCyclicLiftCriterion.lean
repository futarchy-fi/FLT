/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteCyclicCorrection
public import FLT.Mazur.LocalBaseFaithfulMarkingLift

/-!
# An actual faithful cyclic parameter lift from formal-kernel divisibility

The corrected marking factors through the original faithful open because its
closed point does. Thus the only extra lifting hypothesis here is bijectivity
of the nth power map on the original reduction kernel. No such bijectivity is
claimed without a further geometric argument.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
variable (labels : Multiplicative (ZMod n) →*
  (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
variable (hpow : Function.Bijective (fun z : (completeSectionReduction K).ker ↦ z ^ n))
  (hlabels : Function.Injective labels)
local notation "G" => relativeGroup (PowerSeries.X : PowerSeries K)
local notation "L" => Multiplicative (ZMod n)

/-- The corrected equation parameter has exactly the original faithful closed parameter. -/
theorem correctedEquation_reduction :
    completeClosedTestMap K ≫ liftMarking (G).X L
      (correctedCompleteMarking K n labels hpow) =
        closedCyclicParameter K n labels hlabels ≫ faithfulInclusion (G).X L := by
  apply homScheme_ext
  intro a
  rw [Category.assoc, liftMarking_value, correctedCompleteMarking_reduction,
    Category.assoc, closedCyclicParameter_value]

include hlabels in
/-- The closed image of the corrected parameter lies in the actual faithful open. -/
theorem correctedEquation_closedFaithful :
    (liftMarking (G).X L (correctedCompleteMarking K n labels hpow)).left
      (IsLocalRing.closedPoint (PowerSeries K)) ∈ faithfulOpen (G).X L := by
  let _ : IsLocalHom (PowerSeries.constantCoeff : PowerSeries K →+* K) :=
    ⟨fun a ha ↦ PowerSeries.isUnit_iff_constantCoeff.mpr ha⟩
  have hc := IsLocalRing.comap_closedPoint
    (PowerSeries.constantCoeff : PowerSeries K →+* K)
  have he := congrArg (fun f ↦ f.left (IsLocalRing.closedPoint K))
    (correctedEquation_reduction K n labels hpow hlabels)
  change (liftMarking (G).X L (correctedCompleteMarking K n labels hpow)).left
    (PrimeSpectrum.comap PowerSeries.constantCoeff (IsLocalRing.closedPoint K)) = _ at he
  rw [hc] at he
  rw [he]
  exact ((closedCyclicParameter K n labels hlabels).left (IsLocalRing.closedPoint K)).property

/-- Kernel-power bijectivity constructs an actual faithful parameter over the complete base. -/
def correctedCompleteParameter :
    𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶
      relativeCyclicParameter (PowerSeries.X : PowerSeries K) n :=
  localFaithfulLift (G).X L (liftMarking (G).X L
    (correctedCompleteMarking K n labels hpow))
      (correctedEquation_closedFaithful K n labels hpow hlabels)

/-- The faithful parameter retains the whole corrected equation parameter. -/
@[reassoc] theorem correctedCompleteParameter_inclusion :
    correctedCompleteParameter K n labels hpow hlabels ≫ faithfulInclusion (G).X L =
      liftMarking (G).X L (correctedCompleteMarking K n labels hpow) :=
  localFaithfulLift_inclusion _ _ _ _

/-- The actual lifted faithful parameter restricts to the prescribed closed parameter point. -/
@[reassoc] theorem correctedCompleteParameter_reduction :
    completeClosedTestMap K ≫ correctedCompleteParameter K n labels hpow hlabels =
      closedCyclicParameter K n labels hlabels := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (faithfulOpen (G).X L).ι).mp
  have he : (completeClosedTestMap K ≫
      correctedCompleteParameter K n labels hpow hlabels) ≫ faithfulInclusion (G).X L =
        closedCyclicParameter K n labels hlabels ≫ faithfulInclusion (G).X L := by
    rw [Category.assoc, correctedCompleteParameter_inclusion]
    exact correctedEquation_reduction K n labels hpow hlabels
  exact congrArg Over.Hom.left he

end FLT.Mazur.OneGonSmoothing
