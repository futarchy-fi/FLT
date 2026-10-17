/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationAuxiliaryMarking
public import FLT.Mazur.OddWeierstrassCyclicHomRelabelAuxiliary

/-!
# Actual comparison between relabeling before and after normalization

The full relabeling and normalization isomorphisms preserve both independent
markings. No normalized-parameter equality is assumed in this construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] cyclicHomNormalizedPoint
variable (n : ℕ) [NeZero n] (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n)))
  {T : Scheme} (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
local notation "r" => Over.Hom.left (cyclicHomRelabel n a c)
local notation "fN" => cyclicHomNormalizedPoint n f

/-- The actual full comparison of the two relabeled original source families. -/
def cyclicHomRelabeledNormalizationIso :
    (auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n (fN ≫ r))).X ≅
      (auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n (f ≫ r))).X :=
  groupIso (cyclicHomRelabelCurveIso n a c fN) ≪≫
    (CommGrp.forget (Over T)).mapIso (cyclicHomNormalizationGroupIso n f) ≪≫
      (groupIso (cyclicHomRelabelCurveIso n a c f)).symm

/-- All original auxiliary labels commute with the relabeled normalization comparison. -/
theorem cyclicHomRelabeledNormalizationIso_auxiliary (i : Labels 3) :
    cyclicHomFullAuxiliaryMarking n (fN ≫ r) i ≫
      (cyclicHomRelabeledNormalizationIso n a c f).hom =
        cyclicHomFullAuxiliaryMarking n (f ≫ r) i := by
  apply (cancel_mono (groupIso (cyclicHomRelabelCurveIso n a c f)).hom).mp
  simp only [cyclicHomRelabeledNormalizationIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (_ ≫ (cyclicHomRelabelCurveIso n a c fN).hom.group ≫
    (cyclicHomNormalizationGroupIso n f).hom.hom.hom.hom) =
      _ ≫ (cyclicHomRelabelCurveIso n a c f).hom.group
  rw [← Category.assoc, cyclicHomRelabelCurveIso_auxiliary,
    cyclicHomNormalizationGroupIso_fullAuxiliary, cyclicHomRelabelCurveIso_auxiliary]

/-- Every original cyclic label commutes, including coincident values and the zero value. -/
theorem cyclicHomRelabeledNormalizationIso_cyclic (i : Multiplicative (ZMod n)) :
    cyclicHomSourceMarking n (fN ≫ r) i ≫
      (cyclicHomRelabeledNormalizationIso n a c f).hom =
        cyclicHomSourceMarking n (f ≫ r) i := by
  apply (cancel_mono (groupIso (cyclicHomRelabelCurveIso n a c f)).hom).mp
  simp only [cyclicHomRelabeledNormalizationIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (_ ≫ (cyclicHomRelabelCurveIso n a c fN).hom.group ≫
    (cyclicHomNormalizationGroupIso n f).hom.hom.hom.hom) =
      _ ≫ (cyclicHomRelabelCurveIso n a c f).hom.group
  rw [← Category.assoc, cyclicHomRelabelCurveIso_marking,
    cyclicHomNormalizationGroupIso_marking, cyclicHomRelabelCurveIso_marking]

end FLT.Mazur.OddWeierstrassParameter
