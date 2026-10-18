/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOddNormalizedAuxiliary
public import FLT.Mazur.CyclicCharacteristicOddRelabeledGenerator

/-!
# Independent auxiliary frames through the odd relabeled atlas comparison

The actual chart-to-source comparison carries every auxiliary label through
normalization and the common relabeling action to its prescribed original label.
The comparison is the same one that already retains all generator powers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.CyclicCharacteristicAtlas
open OddWeierstrassParameter GeneralizedEllipticCurve
open GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (e : RelabelGroup n) {T : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (h : cyclicHomMultiplicationEquation n f = 0)
local notation "fR" => f ≫
  Over.Hom.left (cyclicHomRelabel n (Prod.fst (Prod.snd e)) (Prod.snd (Prod.snd e)))
local notation "hR" =>
  cyclicHomRelabel_equation n (Prod.fst (Prod.snd e)) (Prod.snd (Prod.snd e)) f h
local notation "qR" => cyclicHomNormalizedLocusPoint n fR hR
local notation "fRN" => cyclicHomNormalizedPoint n fR

/-- The sealed atlas comparison retains its actual auxiliary frame. -/
theorem oddRelabeledAtlasComparison_auxiliary (i : Labels 3) :
    pullSection qR (oddNormalizedAuxiliaryMarking n i) ≫
      (oddRelabeledAtlasComparison n e f h).curve.hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n fRN) i := by
  exact CompatibleIso.group_section_iso_congr
    (oddRelabeledAtlasComparison n e f h) (oddNormalizedSourceIso n fR hR) _ _
    (oddRelabeledAtlasComparison_def n e f h) (oddNormalizedSourceIso_auxiliary n fR hR i)

/-- The sealed normalization comparison retains every independent auxiliary label. -/
theorem oddRelabeledNormalizationComparison_auxiliary (i : Labels 3) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n fRN) i ≫
      (oddRelabeledNormalizationComparison n e f h).curve.hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n fR) i := by
  exact CompatibleIso.group_section_iso_congr
    (oddRelabeledNormalizationComparison n e f h) (cyclicHomNormalizationSubgroupIso n fR hR) _ _
    (oddRelabeledNormalizationComparison_def n e f h)
    (cyclicHomNormalizationSubgroupIso_auxiliary n fR hR i)

/-- The sealed original comparison applies the common auxiliary permutation. -/
theorem oddRelabeledOriginalComparison_auxiliary (i : Labels 3) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n fR) i ≫
      (oddRelabeledOriginalComparison n e f h).curve.hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) (e.2.1.symm i) := by
  exact CompatibleIso.group_section_iso_congr
    (oddRelabeledOriginalComparison n e f h) (cyclicHomRelabelSubgroupIso n e.2.1 e.2.2 f h) _ _
    (oddRelabeledOriginalComparison_def n e f h)
    (cyclicHomRelabelSubgroupIso_auxiliary n e.2.1 e.2.2 f h i)

/-- The full relabeled atlas comparison preserves the prescribed original auxiliary frame. -/
theorem oddRelabeledNormalizedSourceIso_auxiliary (i : Labels 3) :
    pullSection qR (oddNormalizedAuxiliaryMarking n i) ≫
      (oddRelabeledNormalizedSourceIso n e f h).curve.hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) (e.2.1.symm i) := by
  exact CompatibleIso.group_section_trans_three
    (oddRelabeledAtlasComparison n e f h) (oddRelabeledNormalizationComparison n e f h)
    (oddRelabeledOriginalComparison n e f h) _ _ _ _
    (oddRelabeledAtlasComparison_auxiliary n e f h i)
    (oddRelabeledNormalizationComparison_auxiliary n e f h i)
    (oddRelabeledOriginalComparison_auxiliary n e f h i)

end FLT.Mazur.CyclicCharacteristicAtlas
