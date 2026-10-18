/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomSubgroupPullback
public import FLT.Mazur.CompatibleSubgroupOrbitMarking

/-!
# Odd subgroup pullback retains every specified orbit section

The canonical full comparison carries the reconstructed label one to the
pullback of the specified universal generator, including at non-etale levels.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) (k : U ⟶ T)
  (h : cyclicHomMultiplicationEquation n f = 0)
local notation "H" => cyclicHomSubgroup n f h
local notation "HK" => cyclicHomSubgroup n (k ≫ f)
  (cyclicHomMultiplicationEquation_zero_comp n f k h)
local notation "e" => cyclicHomSubgroupPullbackIso n f k h

/-- The subgroup pullback uses the specified full source comparison. -/
theorem cyclicHomSubgroupPullbackIso_curve : (e).curve = cyclicHomSourcePullbackIso n f k := by
  change (Iso.refl _ ≪≫ (cyclicHomSourcePullbackIso n f k).symm.symm) = _
  exact Iso.refl_trans _

/-- All reconstructed orbit sections are the pulled original sections. -/
theorem cyclicHomSubgroupPullbackIso_orbit (i : Multiplicative (ZMod n)) :
    (HK).orbitMarking (cyclicHomSourceMarking n (k ≫ f)) (cyclicHomSubgroup_ideal n _ _) i ≫
      (e).subgroup.hom =
        pullSection k ((H).orbitMarking (cyclicHomSourceMarking n f)
          (cyclicHomSubgroup_ideal n f h) i) := by
  let _ : Mono ((H).baseChange k).inclusion := Over.mono_of_mono_left _
  apply (cancel_mono ((H).baseChange k).inclusion).mp
  rw [Category.assoc, ← CompatibleIso.group_inclusion, ← Category.assoc,
    orbitMarking_inclusion, cyclicHomSubgroupPullbackIso_curve]
  change _ = pullSection k _ ≫ (Over.pullback k).map (H).inclusion
  rw [← section_comp, orbitMarking_inclusion]
  exact cyclicHomSourcePullbackIso_marking n f k i

/-- The chosen generator pulls back under the same full compatible comparison. -/
theorem cyclicHomSubgroupPullbackIso_generator :
    (HK).orbitGenerator (cyclicHomSourceMarking n (k ≫ f)) (cyclicHomSubgroup_ideal n _ _) ≫
      (e).subgroup.hom =
        (H).pullGenerator k ((H).orbitGenerator (cyclicHomSourceMarking n f)
          (cyclicHomSubgroup_ideal n f h)) :=
  cyclicHomSubgroupPullbackIso_orbit n f k h (.ofAdd 1)

end FLT.Mazur.OddWeierstrassParameter
