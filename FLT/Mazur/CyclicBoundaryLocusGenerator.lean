/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryGeneratorComparison
public import FLT.Mazur.CompatibleSubgroupGeneratorMarking

/-!
# Closed boundary comparisons retain the original Cartier generator

The universal residue-one label is an actual generator of the subgroup on
the closed locus. The comparison from an original generated subgroup carries
its prescribed generator to the pullback of this universal generator.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve GroupSectionBaseChange
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [SmoothOfRelativeDimension 1 E.group.hom]

instance unrestrictedLocusCurve_group_smooth :
    SmoothOfRelativeDimension 1 (unrestrictedLocusCurve E n).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1)
    (unrestrictedUniversalCurve E n).group.hom (unrestrictedMultiplicationLocusInclusion E n)
    inferInstance

/-- The original residue-one section in the actual subgroup over the closed locus. -/
def unrestrictedLocusGenerator : 𝟙_ (Over (unrestrictedMultiplicationLocus E n)) ⟶
    (unrestrictedLocusSubgroup E n).carrier :=
  (unrestrictedUniversalCurve E n).singularOrbitLocusGenerator (unrestrictedUniversalMarking E n)

/-- The universal generator is Cartier even when cyclic labels coincide. -/
theorem unrestrictedLocusGenerator_cartier :
    (unrestrictedLocusSubgroup E n).IsCartierGenerator (unrestrictedLocusGenerator E n) :=
  (unrestrictedUniversalCurve E n).singularOrbitLocusGenerator_cartier _

/-- Its group image is exactly the original residue-one label. -/
@[reassoc] theorem unrestrictedLocusGenerator_inclusion :
    unrestrictedLocusGenerator E n ≫ (unrestrictedLocusSubgroup E n).inclusion =
      unrestrictedLocusLabel E n (1, 1, .ofAdd 1) := by
  have h := (unrestrictedLocusCurve E n).singularCyclicDivisorLabel_inclusion
    (pullCyclicMarking (unrestrictedMultiplicationLocusInclusion E n)
      (unrestrictedUniversalMarking E n))
    ((unrestrictedUniversalCurve E n).singularOrbitLocus_multiplication
      (unrestrictedUniversalMarking E n)) 1
  have hm : unrestrictedUniversalMarking E n (.ofAdd 1) =
      markedSection E.group n (parameter E.group n).hom (𝟙 _) (1, 1, .ofAdd 1) :=
    cyclicSectionMarking_apply E.group n _ _ _
  change unrestrictedLocusGenerator E n ≫ (unrestrictedLocusSubgroup E n).inclusion =
    pullSection (unrestrictedMultiplicationLocusInclusion E n)
      (unrestrictedUniversalMarking E n (.ofAdd 1)) at h
  rw [hm] at h
  exact h

variable (g : T ⟶ S) (H : (E.baseChange g).FiniteSubgroup n)
  {P : 𝟙_ (Over T) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
  (a : Labels 4 →* (𝟙_ (Over T) ⟶ (E.baseChange g).group))
  (b : Labels 3 →* (𝟙_ (Over T) ⟶ (E.baseChange g).group))
local notation "k" => generatorLocusLift E n g H hP a b

/-- The full comparison retains the specified original generator itself. -/
theorem generatorLocusSubgroupIso_generator :
    P ≫ (generatorLocusSubgroupIso E n g H hP a b).subgroup.hom =
      pullSection (k) (unrestrictedLocusGenerator E n) := by
  let d := generatorLocusSubgroupIso E n g H hP a b
  let J := (unrestrictedLocusSubgroup E n).baseChange (k)
  let _ : Mono J.inclusion := Over.mono_of_mono_left J.inclusion
  have hP' : H.generatorCurveMarking hP (.ofAdd 1) = P ≫ H.inclusion := by
    change H.generatorPowers P hP.1 (.ofAdd 1) ≫ H.inclusion = _
    have hp := H.generatorPowers_natCast P hP.1 1
    simpa only [Nat.cast_one, pow_one] using congrArg (· ≫ H.inclusion) hp
  apply (cancel_mono J.inclusion).mp
  change (P ≫ d.subgroup.hom) ≫ J.inclusion =
    pullSection (k) (unrestrictedLocusGenerator E n) ≫
      (Over.pullback (k)).map (unrestrictedLocusSubgroup E n).inclusion
  rw [Category.assoc, ← d.group_inclusion, ← Category.assoc, ← hP',
    ← section_comp, unrestrictedLocusGenerator_inclusion]
  simpa only [map_one, _root_.one_mul] using
    generatorLocusSubgroupIso_label E n g H hP a b (1, 1, .ofAdd 1)

end FLT.Mazur.CyclicBoundaryParameter
