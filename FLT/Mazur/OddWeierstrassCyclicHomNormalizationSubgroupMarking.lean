/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationSubgroup
public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationAuxiliaryMarking
public import FLT.Mazur.CompatibleSubgroupOrbitMarking

/-!
# Normalization retains the prescribed subgroup and auxiliary labels

The actual compatible subgroup comparison preserves its specified orbit
sections and Cartier generator, together with the independent auxiliary frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (h : cyclicHomMultiplicationEquation n f = 0)
local notation "fN" => cyclicHomNormalizedPoint n f
local notation "hN" => cyclicHomNormalization_equation n f h
local notation "H" => cyclicHomSubgroup n f h
local notation "HN" => cyclicHomSubgroup n fN hN
local notation "e" => cyclicHomNormalizationSubgroupIso n f h

/-- The actual compatible subgroup comparison has the prescribed normalization curve. -/
theorem cyclicHomNormalizationSubgroupIso_curve :
    (e).curve = cyclicHomNormalizationCurveIso n f := by
  change (Iso.refl _ ≪≫ (cyclicHomNormalizationCurveIso n f).symm.symm) = _
  exact Iso.refl_trans _

/-- Every specified cyclic label survives on the actual subgroup carrier. -/
theorem cyclicHomNormalizationSubgroupIso_orbit (i : Multiplicative (ZMod n)) :
    (HN).orbitMarking (cyclicHomSourceMarking n fN) (cyclicHomSubgroup_ideal n fN hN) i ≫
      (e).subgroup.hom =
        (H).orbitMarking (cyclicHomSourceMarking n f) (cyclicHomSubgroup_ideal n f h) i := by
  apply CompatibleIso.orbitMarking_eq
  rw [cyclicHomNormalizationSubgroupIso_curve]
  exact cyclicHomNormalizationGroupIso_marking n f i

/-- The chosen universal generator, rather than merely some generator, is retained. -/
theorem cyclicHomNormalizationSubgroupIso_generator :
    (HN).orbitGenerator (cyclicHomSourceMarking n fN) (cyclicHomSubgroup_ideal n fN hN) ≫
      (e).subgroup.hom =
        (H).orbitGenerator (cyclicHomSourceMarking n f) (cyclicHomSubgroup_ideal n f h) := by
  dsimp only [orbitGenerator]
  exact cyclicHomNormalizationSubgroupIso_orbit n f h (.ofAdd 1)

/-- The same full compatible comparison retains each independent auxiliary label. -/
theorem cyclicHomNormalizationSubgroupIso_auxiliary (i : Labels 3) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n fN) i ≫ (e).curve.hom.group =
      auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i := by
  rw [cyclicHomNormalizationSubgroupIso_curve]
  exact cyclicHomNormalizationGroupIso_auxiliary n f i

end FLT.Mazur.OddWeierstrassParameter
