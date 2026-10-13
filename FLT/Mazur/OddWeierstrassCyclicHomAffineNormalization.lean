/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomAffineSubgroup
public import FLT.Mazur.OddWeierstrassNormalizedSubgroupLocus

/-!
# Normalized locus points for actual affine cyclic sources

An original Cartier generator gives a normalized parameter whose universal
subgroup is compatibly isomorphic to the entire original finite subgroup.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {n : ℕ} [NeZero n]
  (f : Spec (.of R) ⟶ (cyclicHomAuxiliaryScheme n).left)
  (H : (cyclicHomSourceCurve n f).FiniteSubgroup n)
  {P : 𝟙_ (Over (Spec (.of R))) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
local notation "a" => cyclicHomAuxiliaryPoint n f
local notation "g" => auxiliaryPointSections a

/-- Normalize the actual affine family with its original Cartier subgroup. -/
def cyclicHomAffineNormalizedLocusPoint :
    Spec (.of R) ⟶ cyclicHomUniversalMultiplicationLocus n :=
  auxiliaryNormalizedSubgroupLocusPoint g (auxiliaryRelativePoint a)
    (cyclicHomAffineSubgroup f H) (cyclicHomAffineSubgroup_generator f H hP)

/-- The normalized point represents the entire original curve and finite subgroup. -/
def cyclicHomAffineNormalizedLocusIso :
    CompatibleIso ((cyclicHomUniversalSubgroup n).baseChange
      (cyclicHomAffineNormalizedLocusPoint f H hP)) H :=
  (auxiliaryNormalizedSubgroupLocusIso g (auxiliaryRelativePoint a)
    (cyclicHomAffineSubgroup f H) (cyclicHomAffineSubgroup_generator f H hP)).trans
      (cyclicHomAffineSubgroupIso f H).symm

/-- Its auxiliary coordinate is precisely the normalized original auxiliary point. -/
@[reassoc] theorem cyclicHomAffineNormalizedLocusPoint_auxiliary :
    cyclicHomAffineNormalizedLocusPoint f H hP ≫
      cyclicHomUniversalMultiplicationLocusInclusion n ≫ (cyclicHomAuxiliary n).left =
        auxiliaryFamilyNormalizedPoint a := by
  rw [← Category.assoc]
  unfold cyclicHomAffineNormalizedLocusPoint
  rw [auxiliaryNormalizedSubgroupLocusPoint_inclusion]
  rw [← Over.comp_left, auxiliaryNormalizedCyclicParameter_auxiliary]
  rw [auxiliaryFamilyNormalizedPoint_def]

end FLT.Mazur.OddWeierstrassParameter
