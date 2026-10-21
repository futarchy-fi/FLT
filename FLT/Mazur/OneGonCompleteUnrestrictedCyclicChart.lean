/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteGroupRelativeDimension
public import FLT.Mazur.CyclicBoundaryUnrestrictedAmpleCoverage

/-!
# Unrestricted cyclic charts over the entire complete one-gon family

The closed orbit locus and its ample open use the original complete family,
including its generic and singular fibers. Cyclic rank is independent of the
family, and all original auxiliary labels and subgroup generators are retained.
These charts do not assert versality for other singular degenerations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.OneGonSmoothing
open CyclicBoundaryParameter GeneralizedEllipticCurve GroupSectionBaseChange
open GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
local notation "E" => completeGeneralizedCurve K

/-- The full closed cyclic locus over the actual complete coefficient family. -/
def completeUnrestrictedCyclicChart : Scheme := unrestrictedMultiplicationLocus (E) n

/-- The closed embedding in the full independent auxiliary and cyclic parameter scheme. -/
def completeUnrestrictedCyclicChartInclusion : completeUnrestrictedCyclicChart K n ⟶
    (CyclicBoundaryParameter.parameter (E).group n).left :=
  unrestrictedMultiplicationLocusInclusion (E) n

instance completeUnrestrictedCyclicChartInclusion_closed :
    IsClosedImmersion (completeUnrestrictedCyclicChartInclusion K n) :=
  unrestrictedMultiplicationLocusInclusion_closed (E) n

/-- Ampleness gives an actual open in the original complete-family closed chart. -/
def completeUnrestrictedAmpleChart : (completeUnrestrictedCyclicChart K n).Opens :=
  unrestrictedAmpleOpen (E) n

/-- The chart carries the full original pulled-back curve and its actual ample subgroup. -/
def completeUnrestrictedAmpleLevel :
    ampleCyclicLevels (completeUnrestrictedAmpleChart K n).toScheme n :=
  unrestrictedAmpleLevel (E) n

/-- This whole-family chart covers every ample cyclic test with its original full markings. -/
theorem exists_completeUnrestrictedAmpleChart_test {T : Scheme}
    (g : T ⟶ Spec (.of (PowerSeries K)))
    (H : ((E).baseChange g).FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple)
    (a : Labels 4 →* (𝟙_ (Over T) ⟶ ((E).baseChange g).group))
    (b : Labels 3 →* (𝟙_ (Over T) ⟶ ((E).baseChange g).group)) :
    ∃ (U : Scheme) (q : U ⟶ T), Flat q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧
      ∃ (P : 𝟙_ (Over U) ⟶ (H.baseChange q).carrier)
        (_ : (H.baseChange q).IsCartierGenerator P)
        (v : U ⟶ (completeUnrestrictedAmpleChart K n).toScheme)
        (d : FiniteSubgroup.CompatibleIso (H.baseChange q)
          ((completeUnrestrictedAmpleLevel K n).val.2.baseChange v)),
        (∀ j, pullSection q (a j) ≫ d.curve.hom.group =
          pullSection v (unrestrictedAmpleLabel (E) n (j, 1, 1))) ∧
        (∀ j, pullSection q (b j) ≫ d.curve.hom.group =
          pullSection v (unrestrictedAmpleLabel (E) n (1, j, 1))) ∧
        P ≫ d.subgroup.hom = pullSection v (unrestrictedAmpleGenerator (E) n) :=
  exists_original_unrestricted_marked_ample_test (E) n g H hc ha a b

end FLT.Mazur.OneGonSmoothing
