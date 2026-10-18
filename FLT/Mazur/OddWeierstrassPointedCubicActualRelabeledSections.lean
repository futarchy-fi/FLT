/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassPointedCubicHomOriginalSections
public import FLT.Mazur.CyclicCharacteristicOddRelabeledAuxiliary

/-!
# Relabeled normalized atlas comparisons with the original prescribed cubic

The common finite relabeling action compares the actual normalized atlas
subgroup all the way to the original cubic subgroup. The comparison carries
both the permuted auxiliary frame and the specified generator powers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve CyclicCharacteristicAtlas
open GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₃ : IsUnit (3 : Γ(S, ⊤))) {n : ℕ} [NeZero n] (e : RelabelGroup n)
  (H : (pointedCubicFamily W).FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
local notation "φ" => H.generatorCurveMarking hP
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₃)
local notation "f" => Over.Hom.left (pointedCubicHomAuxiliaryParameter W h₃ φ)
local notation "hf" => pointedCubicHomPrescribed_equation W h₃ H hP
local notation "fR" => f ≫
  Over.Hom.left (cyclicHomRelabel n (Prod.fst (Prod.snd e)) (Prod.snd (Prod.snd e)))
local notation "hR" =>
  cyclicHomRelabel_equation n (Prod.fst (Prod.snd e)) (Prod.snd (Prod.snd e)) f hf
local notation "qR" => cyclicHomNormalizedLocusPoint n fR hR

/-- The actual relabeled chart compares with the original full cubic subgroup. -/
def pointedCubicActualRelabeledIso :
    CompatibleIso ((normalizedSubgroup n true).baseChange qR) (H.baseChange k) :=
  (oddRelabeledNormalizedSourceIso n e f hf).trans (pointedCubicHomOriginalIso W h₃ H hP)

/-- Every independent auxiliary label reaches its prescribed original relabeling. -/
theorem pointedCubicActualRelabeledIso_auxiliary (i : Labels 3) :
    pullSection qR (oddNormalizedAuxiliaryMarking n i) ≫
      (pointedCubicActualRelabeledIso W h₃ e H hP).curve.hom.group =
        pointedCubicOriginalAuxiliaryMarking W h₃ (e.2.1.symm i) := by
  exact CompatibleIso.group_section_trans (oddRelabeledNormalizedSourceIso n e f hf)
    (pointedCubicHomOriginalIso W h₃ H hP) _ _ _
    (oddRelabeledNormalizedSourceIso_auxiliary n e f hf i)
    (pointedCubicHomOriginalIso_auxiliary W h₃ H hP (e.2.1.symm i))

/-- Every atlas generator power has the prescribed relabeled value in the original subgroup. -/
theorem pointedCubicActualRelabeledIso_generator_pow (m : ℕ) :
    (pullSection qR (oddNormalizedGenerator n) ^ m) ≫
      (pointedCubicActualRelabeledIso W h₃ e H hP).subgroup.hom =
        pullSection k (P ^ (e.2.2.symm (.ofAdd (m : ZMod n))).toAdd.val) := by
  change _ ≫ ((oddRelabeledNormalizedSourceIso n e f hf).subgroup.hom ≫
    (pointedCubicHomOriginalIso W h₃ H hP).subgroup.hom) = _
  rw [← Category.assoc, oddRelabeledNormalizedSourceIso_generator_pow]
  exact pointedCubicHomOriginalIso_orbit W h₃ H hP _

end FLT.Mazur.OddWeierstrassParameter
