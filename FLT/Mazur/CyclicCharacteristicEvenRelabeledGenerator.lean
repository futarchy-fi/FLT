/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupSectionComposition
public import FLT.Mazur.CyclicCharacteristicEvenNormalizedGenerator
public import FLT.Mazur.CyclicHomNormalizationSubgroupMarking
public import FLT.Mazur.CyclicHomRelabelSubgroupMarking

/-!
# Common finite relabelings on the actual even normalized subgroup generator

Relabel an original parameter and normalize it. The resulting actual atlas
subgroup compares with the original source subgroup, and its chosen generator
powers are exactly the original orbit labels under the common cyclic permutation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
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
local notation "H" => cyclicHomSubgroup n f h

/-- The normalized relabeled parameter is exactly the existing common finite group action. -/
theorem evenNormalizedPoint_relabel :
    cyclicHomNormalizedLocusPoint n f h ≫ (normalizedRelabelAction n false e).hom = qR := by
  let l := cyclicHomUniversalLocusLift n f h
  have hl : l ≫ cyclicHomLocusNormalization n = cyclicHomNormalizedLocusPoint n f h := by
    rw [cyclicHomLocusNormalization_comp]
    simp only [l, cyclicHomUniversalLocusLift_inclusion]
  rw [← hl, Category.assoc]
  change l ≫ cyclicHomLocusNormalization n ≫ cyclicHomNormalizedRelabel n e.1 e.2.2 = _
  rw [cyclicHomLocusNormalization_equivariant, ← Category.assoc,
    cyclicHomLocusNormalization_comp]
  have hp : (l ≫ cyclicHomLocusRelabel n e.1 e.2.2) ≫
      cyclicHomUniversalMultiplicationLocusInclusion n = fR := by
    rw [Category.assoc, cyclicHomLocusRelabel_inclusion, ← Category.assoc]
    exact congrArg (fun z ↦ z ≫ (cyclicHomRelabel n e.1 e.2.2).left)
      (cyclicHomUniversalLocusLift_inclusion n f h)
  simp only [hp]

local notation "HR" => cyclicHomSubgroup n fR hR
local notation "fRN" => cyclicHomNormalizedPoint n fR
local notation "hRN" => cyclicHomNormalization_equation n fR hR
local notation "HRN" => cyclicHomSubgroup n fRN hRN

/-- Seal the actual atlas comparison at the relabeled test. -/
irreducible_def evenRelabeledAtlasComparison := evenNormalizedSourceIso n fR hR

/-- The sealed atlas comparison retains its specified normalized generator. -/
theorem evenRelabeledAtlasComparison_generator :
    pullSection qR (evenNormalizedGenerator n) ≫
      (evenRelabeledAtlasComparison n e f h).subgroup.hom =
        (HRN).orbitGenerator (cyclicHomSourceMarking n fRN)
          (cyclicHomSubgroup_ideal n fRN hRN) := by
  exact CompatibleIso.subgroup_section_iso_congr
    (evenRelabeledAtlasComparison n e f h) (evenNormalizedSourceIso n fR hR) _ _
    (evenRelabeledAtlasComparison_def n e f h) (evenNormalizedSourceIso_generator n fR hR)

/-- Seal the full normalization comparison of the relabeled original subgroup. -/
irreducible_def evenRelabeledNormalizationComparison :=
  cyclicHomNormalizationSubgroupIso n fR hR

/-- The sealed normalization comparison retains the relabeled source generator. -/
theorem evenRelabeledNormalizationComparison_generator :
    (HRN).orbitGenerator (cyclicHomSourceMarking n fRN)
      (cyclicHomSubgroup_ideal n fRN hRN) ≫
        (evenRelabeledNormalizationComparison n e f h).subgroup.hom =
          (HR).orbitGenerator (cyclicHomSourceMarking n fR)
            (cyclicHomSubgroup_ideal n fR hR) := by
  exact CompatibleIso.subgroup_section_iso_congr
    (evenRelabeledNormalizationComparison n e f h) (cyclicHomNormalizationSubgroupIso n fR hR) _ _
    (evenRelabeledNormalizationComparison_def n e f h)
    (cyclicHomNormalizationSubgroupIso_generator n fR hR)

/-- Seal the relabeling comparison with the original full source subgroup. -/
irreducible_def evenRelabeledOriginalComparison :=
  cyclicHomRelabelSubgroupIso n e.1 e.2.2 f h

/-- The sealed original comparison retains the prescribed relabeled orbit value. -/
theorem evenRelabeledOriginalComparison_generator :
    (HR).orbitGenerator (cyclicHomSourceMarking n fR) (cyclicHomSubgroup_ideal n fR hR) ≫
      (evenRelabeledOriginalComparison n e f h).subgroup.hom =
        (H).orbitMarking (cyclicHomSourceMarking n f) (cyclicHomSubgroup_ideal n f h)
          (e.2.2.symm (.ofAdd 1)) := by
  exact CompatibleIso.subgroup_section_iso_congr
    (evenRelabeledOriginalComparison n e f h) (cyclicHomRelabelSubgroupIso n e.1 e.2.2 f h) _ _
    (evenRelabeledOriginalComparison_def n e f h)
    (by simpa only [pow_one, Nat.cast_one] using
      cyclicHomRelabelSubgroupIso_generator_pow n e.1 e.2.2 f h 1)

/-- The common relabeling retains the actual full original source subgroup on the even chart. -/
def evenRelabeledNormalizedSourceIso :
    CompatibleIso ((normalizedSubgroup n false).baseChange qR) (H) :=
  (evenRelabeledAtlasComparison n e f h).trans
    ((evenRelabeledNormalizationComparison n e f h).trans
      (evenRelabeledOriginalComparison n e f h))

/-- The actual even atlas generator has the prescribed relabeled original orbit value. -/
theorem evenRelabeledNormalizedSourceIso_generator :
    pullSection qR (evenNormalizedGenerator n) ≫
      (evenRelabeledNormalizedSourceIso n e f h).subgroup.hom =
        (H).orbitMarking (cyclicHomSourceMarking n f) (cyclicHomSubgroup_ideal n f h)
          (e.2.2.symm (.ofAdd 1)) := by
  exact CompatibleIso.subgroup_section_trans_three
    (evenRelabeledAtlasComparison n e f h) (evenRelabeledNormalizationComparison n e f h)
    (evenRelabeledOriginalComparison n e f h) _ _ _ _
    (evenRelabeledAtlasComparison_generator n e f h)
    (evenRelabeledNormalizationComparison_generator n e f h)
    (evenRelabeledOriginalComparison_generator n e f h)

/-- Every generator power uses the same common cyclic permutation on the original subgroup. -/
theorem evenRelabeledNormalizedSourceIso_generator_pow (m : ℕ) :
    (pullSection qR (evenNormalizedGenerator n) ^ m) ≫
      (evenRelabeledNormalizedSourceIso n e f h).subgroup.hom =
        (H).orbitMarking (cyclicHomSourceMarking n f) (cyclicHomSubgroup_ideal n f h)
          (e.2.2.symm (.ofAdd (m : ZMod n))) := by
  simp only [MonObj.pow_comp, evenRelabeledNormalizedSourceIso_generator, ← map_pow,
    ← ofAdd_nsmul, nsmul_eq_mul, _root_.mul_one]

end FLT.Mazur.CyclicCharacteristicAtlas
