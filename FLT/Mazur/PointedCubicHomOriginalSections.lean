/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicActualNormalizedAuxiliary

/-!
# The reconstructed source retains the original cubic and its prescribed sections

Equality of the orbit ideal compares the reconstructed source with the retained
original subgroup. The inverse cubic comparison then recovers the actual
original auxiliary sections and every power of the prescribed generator.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open UniversalWeierstrass CyclicCharacteristicAtlas FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₂ : IsUnit (2 : Γ(S, ⊤))) {n : ℕ} [NeZero n]
  (H : (pointedCubicFamily W).FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
local notation "φ" => H.generatorCurveMarking hP
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₂)
local notation "f" => Over.Hom.left (pointedCubicHomAuxiliaryParameter W h₂ φ)
local notation "hf" => pointedCubicHomPrescribed_equation W h₂ H hP
local notation "J" => pointedCubicHomRetainedSubgroup W h₂ φ H
local notation "hJ" => pointedCubicHomRetained_ideal W h₂ φ H hP rfl

/-- Compare the reconstructed source with the original full cubic and finite subgroup. -/
def pointedCubicHomOriginalIso :
    CompatibleIso (cyclicHomSubgroup n f hf) (H.baseChange k) :=
  (cyclicHomPrescribedSubgroupIso n f hf J hJ).trans
    (pointedCubicHomRetainedIso W h₂ φ H).symm

/-- The full source comparison retains every original independent auxiliary label. -/
theorem pointedCubicHomOriginalIso_auxiliary (i : Labels 4) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i ≫
      (pointedCubicHomOriginalIso W h₂ H hP).curve.hom.group =
        pointedCubicOriginalAuxiliaryMarking W h₂ i := by
  apply CompatibleIso.group_section_trans (cyclicHomPrescribedSubgroupIso n f hf J hJ)
    (pointedCubicHomRetainedIso W h₂ φ H).symm _
    (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i) _
  · exact Category.comp_id _
  · exact CompatibleIso.group_section_symm (pointedCubicHomRetainedIso W h₂ φ H) _ _
      (pointedCubicHomSourceCurveIso_auxiliary W h₂ φ i)

/-- The actual source orbit generator recovers the originally prescribed Cartier generator. -/
theorem pointedCubicHomOriginalIso_generator :
    (cyclicHomSubgroup n f hf).orbitGenerator (cyclicHomSourceMarking n f)
      (cyclicHomSubgroup_ideal n f hf) ≫
        (pointedCubicHomOriginalIso W h₂ H hP).subgroup.hom = pullSection k P := by
  change _ ≫ ((cyclicHomPrescribedSubgroupIso n f hf J hJ).subgroup.hom ≫
    (pointedCubicHomRetainedIso W h₂ φ H).subgroup.inv) = _
  rw [← Category.assoc, cyclicHomPrescribedSubgroupIso_generator n f hf J hJ
    (pointedCubicHomRetained_generator W h₂ φ H hP)
    (pointedCubicHomRetained_marking W h₂ φ H hP rfl)]
  exact Category.comp_id _

/-- Every cyclic orbit value recovers the actual corresponding original generator power. -/
theorem pointedCubicHomOriginalIso_orbit (i : Multiplicative (ZMod n)) :
    (cyclicHomSubgroup n f hf).orbitMarking (cyclicHomSourceMarking n f)
      (cyclicHomSubgroup_ideal n f hf) i ≫
        (pointedCubicHomOriginalIso W h₂ H hP).subgroup.hom =
          pullSection k (P ^ i.toAdd.val) := by
  have hi : Multiplicative.ofAdd (i.toAdd.val : ZMod n) = i := by simp
  have hp := congrArg (· ≫ (pointedCubicHomOriginalIso W h₂ H hP).subgroup.hom)
    (orbitGenerator_pow (cyclicHomSubgroup n f hf) (cyclicHomSourceMarking n f)
      (cyclicHomSubgroup_ideal n f hf) i.toAdd.val)
  rw [hi, MonObj.pow_comp, pointedCubicHomOriginalIso_generator, ← section_pow] at hp
  exact hp.symm

end FLT.Mazur.GeneralizedEllipticCurve
