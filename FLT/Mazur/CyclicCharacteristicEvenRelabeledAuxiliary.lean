/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicEvenNormalizedAuxiliary
public import FLT.Mazur.CyclicCharacteristicEvenRelabeledGenerator

/-!
# Independent auxiliary frames through the even relabeled atlas comparison

The actual chart-to-source comparison carries every auxiliary label through
normalization and the common relabeling action to its prescribed original label.
The comparison is the same one that already retains all generator powers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.CyclicCharacteristicAtlas
open UniversalWeierstrass GeneralizedEllipticCurve
open GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (e : RelabelGroup n) {T : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (h : cyclicHomMultiplicationEquation n f = 0)
local notation "fR" => f ≫
  Over.Hom.left (cyclicHomRelabel n (Prod.fst e) (Prod.snd (Prod.snd e)))
local notation "hR" =>
  cyclicHomRelabel_equation n (Prod.fst e) (Prod.snd (Prod.snd e)) f h
local notation "qR" => cyclicHomNormalizedLocusPoint n fR hR
local notation "fRN" => cyclicHomNormalizedPoint n fR

/-- The sealed atlas comparison retains its actual auxiliary frame. -/
theorem evenRelabeledAtlasComparison_auxiliary (i : Labels 4) :
    pullSection qR (evenNormalizedAuxiliaryMarking n i) ≫
      (evenRelabeledAtlasComparison n e f h).curve.hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n fRN) i := by
  exact CompatibleIso.group_section_iso_congr
    (evenRelabeledAtlasComparison n e f h) (evenNormalizedSourceIso n fR hR) _ _
    (evenRelabeledAtlasComparison_def n e f h) (evenNormalizedSourceIso_auxiliary n fR hR i)

/-- The sealed normalization comparison retains every independent auxiliary label. -/
theorem evenRelabeledNormalizationComparison_auxiliary (i : Labels 4) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n fRN) i ≫
      (evenRelabeledNormalizationComparison n e f h).curve.hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n fR) i := by
  exact CompatibleIso.group_section_iso_congr
    (evenRelabeledNormalizationComparison n e f h) (cyclicHomNormalizationSubgroupIso n fR hR) _ _
    (evenRelabeledNormalizationComparison_def n e f h)
    (cyclicHomNormalizationSubgroupIso_auxiliary n fR hR i)

/-- The sealed original comparison applies the common auxiliary permutation. -/
theorem evenRelabeledOriginalComparison_auxiliary (i : Labels 4) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n fR) i ≫
      (evenRelabeledOriginalComparison n e f h).curve.hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) (e.1.symm i) := by
  exact CompatibleIso.group_section_iso_congr
    (evenRelabeledOriginalComparison n e f h) (cyclicHomRelabelSubgroupIso n e.1 e.2.2 f h) _ _
    (evenRelabeledOriginalComparison_def n e f h)
    (cyclicHomRelabelSubgroupIso_auxiliary n e.1 e.2.2 f h i)

/-- The full relabeled atlas comparison preserves the prescribed original auxiliary frame. -/
theorem evenRelabeledNormalizedSourceIso_auxiliary (i : Labels 4) :
    pullSection qR (evenNormalizedAuxiliaryMarking n i) ≫
      (evenRelabeledNormalizedSourceIso n e f h).curve.hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) (e.1.symm i) := by
  exact CompatibleIso.group_section_trans_three
    (evenRelabeledAtlasComparison n e f h) (evenRelabeledNormalizationComparison n e f h)
    (evenRelabeledOriginalComparison n e f h) _ _ _ _
    (evenRelabeledAtlasComparison_auxiliary n e f h i)
    (evenRelabeledNormalizationComparison_auxiliary n e f h i)
    (evenRelabeledOriginalComparison_auxiliary n e f h i)

end FLT.Mazur.CyclicCharacteristicAtlas
