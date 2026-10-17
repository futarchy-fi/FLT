/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomRelabelSubgroup
public import FLT.Mazur.CyclicHomRelabelAuxiliaryMarking
public import FLT.Mazur.CompatibleSubgroupOrbitMarking

/-!
# Relabeling retains the prescribed subgroup and auxiliary labels

The actual compatible subgroup comparison carries its orbit sections and
generator by the prescribed permutations, together with the auxiliary frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (a : MulAut (Labels 4)) (c : MulAut (Multiplicative (ZMod n)))
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (h : cyclicHomMultiplicationEquation n f = 0)
local notation "fN" => f ≫ Over.Hom.left (cyclicHomRelabel n a c)
local notation "hN" => cyclicHomRelabel_equation n a c f h
local notation "H" => cyclicHomSubgroup n f h
local notation "HN" => cyclicHomSubgroup n fN hN
local notation "e" => cyclicHomRelabelSubgroupIso n a c f h

/-- The actual compatible subgroup comparison has the prescribed relabeling curve. -/
theorem cyclicHomRelabelSubgroupIso_curve :
    (e).curve = cyclicHomRelabelCurveIso n a c f := by
  change (Iso.refl _ ≪≫ (cyclicHomRelabelCurveIso n a c f).symm.symm) = _
  exact Iso.refl_trans _

/-- Every specified cyclic label survives on the actual subgroup carrier. -/
theorem cyclicHomRelabelSubgroupIso_orbit (i : Multiplicative (ZMod n)) :
    (HN).orbitMarking (cyclicHomSourceMarking n fN) (cyclicHomSubgroup_ideal n fN hN) i ≫
      (e).subgroup.hom =
        (H).orbitMarking (cyclicHomSourceMarking n f) (cyclicHomSubgroup_ideal n f h)
          (c.symm i) := by
  apply CompatibleIso.orbitMarking_eq
  rw [cyclicHomRelabelSubgroupIso_curve]
  exact cyclicHomRelabelCurveIso_marking n a c f i

/-- Relabeling identifies every power of the actual specified generator. -/
theorem cyclicHomRelabelSubgroupIso_generator_pow (m : ℕ) :
    ((HN).orbitGenerator (cyclicHomSourceMarking n fN)
      (cyclicHomSubgroup_ideal n fN hN) ^ m) ≫ (e).subgroup.hom =
        (H).orbitMarking (cyclicHomSourceMarking n f) (cyclicHomSubgroup_ideal n f h)
          (c.symm (.ofAdd (m : ZMod n))) := by
  rw [orbitGenerator_pow]
  exact cyclicHomRelabelSubgroupIso_orbit n a c f h _

/-- The same full compatible comparison retains each independent auxiliary label. -/
theorem cyclicHomRelabelSubgroupIso_auxiliary (i : Labels 4) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n fN) i ≫ (e).curve.hom.group =
      auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) (a.symm i) := by
  rw [cyclicHomRelabelSubgroupIso_curve]
  exact cyclicHomRelabelCurveIso_auxiliary n a c f i

end FLT.Mazur.UniversalWeierstrass
