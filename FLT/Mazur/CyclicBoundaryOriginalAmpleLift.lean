/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryLiftSubgroup
public import FLT.Mazur.CyclicBoundaryAmpleModuli

/-!
# Original faithful ample boundary tests factor through the constructed open

The lift retains the original map, full curve, and finite subgroup. Its modular
class is identified by the actual compatible isomorphism, on arbitrary tests.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
  {T : Scheme} (g : T ⟶ S) (f : Over.mk g ⟶ parameter E.group n)
  (hf : UniversallyDistinctSections.UniversallyDistinct
    (fun i : ZMod n ↦ cyclicSectionMarking E.group n g f (.ofAdd i)))
  (ha : ((E.baseChange g).relativeCyclicSubgroup
    (cyclicSectionMarking E.group n g f) hf).IsAmple)
local notation "H" => faithfulUniversalSubgroup E n
local notation "u" => cyclicFaithfulLift E.group n g f hf
local notation "J" => GeneralizedEllipticCurve.relativeCyclicSubgroup
  (E.baseChange g) (cyclicSectionMarking E.group n g f) hf

/-- The original faithful ample parameter test lifts to the actual constructed open. -/
def originalAmpleLift : T ⟶ ampleParameter E n :=
  (H).ampleOpenLift (faithfulUniversalSubgroup_cartier E n).1 (u).left
    ((cyclicFaithfulLiftSubgroupIso E n g f hf).isAmple_iff.mp ha)

/-- The ample lift retains the full faithful parameter. -/
@[reassoc] theorem originalAmpleLift_faithful :
    originalAmpleLift E n g f hf ha ≫ (ampleParameterOpen E n).ι = (u).left :=
  (H).ampleOpenLift_inclusion _ _ _

/-- The ample lift retains all original parameter labels exactly. -/
@[reassoc] theorem originalAmpleLift_parameter :
    originalAmpleLift E n g f hf ha ≫ ampleParameterInclusion E n = f.left := by
  change originalAmpleLift E n g f hf ha ≫ (ampleParameterOpen E n).ι ≫
    (cyclicFaithfulInclusion E.group n).left = _
  rw [originalAmpleLift_faithful_assoc]
  exact congrArg Over.Hom.left (cyclicFaithfulLift_inclusion E.group n g f hf)

/-- The factorization is unique as a morphism of schemes, including on nonreduced tests. -/
theorem originalAmpleLift_unique (v : T ⟶ ampleParameter E n)
    (hv : v ≫ ampleParameterInclusion E n = f.left) : v = originalAmpleLift E n g f hf ha := by
  apply (cancel_mono (ampleParameterInclusion E n)).mp
  exact hv.trans (originalAmpleLift_parameter E n g f hf ha).symm

/-- The lifted universal level retains the original full test curve and subgroup. -/
def originalAmpleLiftSubgroupIso :
    CompatibleIso (J) ((ampleUniversalLevel E n).val.2.baseChange
      (originalAmpleLift E n g f hf ha)) := by
  have c := cyclicFaithfulLiftSubgroupIso E n g f hf
  rw [← originalAmpleLift_faithful E n g f hf ha] at c
  exact c.trans ((H).compatibleBaseChangeComp (ampleParameterOpen E n).ι
    (originalAmpleLift E n g f hf ha))

/-- The original data define the same actual ample cyclic level as the constructed chart. -/
def originalAmpleTestLevel : ampleCyclicLevels T n :=
  ⟨⟨E.baseChange g, (J)⟩, (originalAmpleLiftSubgroupIso E n g f hf ha).ampleCyclic_iff.mpr
    (ampleCyclicLevelsPullback (originalAmpleLift E n g f hf ha) n
      (ampleUniversalLevel E n)).property⟩

/-- The modular transformation at the lift is exactly the original full test's class. -/
theorem ampleModuliMap_originalAmpleLift :
    (ampleModuliMap E n).app (Opposite.op T) (ULift.up (originalAmpleLift E n g f hf ha)) =
      Quotient.mk _ (originalAmpleTestLevel E n g f hf ha) :=
  Quotient.sound ⟨(originalAmpleLiftSubgroupIso E n g f hf ha).symm⟩

end FLT.Mazur.CyclicBoundaryParameter
