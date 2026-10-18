/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicActualRelabeledSections
public import FLT.Mazur.CyclicLocalOriginalAuxiliary

/-!
# Common relabeling on original local cubic neighborhoods

Compose the actual relabeled atlas comparison with the original local cubic
comparison. It retains the permuted independent frame and every prescribed
generator power on the direct original subgroup pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass CyclicCharacteristicAtlas GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ}
  (H : E.FiniteSubgroup n) (f : T ⟶ S)
  (W : WeierstrassCurve Γ(T, ⊤)) [W.IsElliptic] (h₂ : IsUnit (2 : Γ(T, ⊤)))
  (J : (pointedCubicFamily W).FiniteSubgroup n) (a : CompatibleIso J (H.baseChange f))
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₂)
local notation "d" => CompatibleIso.trans (CompatibleIso.baseChange a k)
  (CompatibleIso.symm (compatibleBaseChangeComp H f k))

variable [NeZero n] (e : RelabelGroup n) {Q : 𝟙_ (Over T) ⟶ J.carrier} (hQ : J.IsCartierGenerator Q)
local notation "p" => Over.Hom.left (pointedCubicHomAuxiliaryParameter W h₂
  (J.generatorCurveMarking hQ))
local notation "hz" => pointedCubicHomPrescribed_equation W h₂ J hQ
local notation "pR" => p ≫ Over.Hom.left
  (cyclicHomRelabel n (Prod.fst e) (Prod.snd (Prod.snd e)))
local notation "hR" => cyclicHomRelabel_equation n (Prod.fst e)
  (Prod.snd (Prod.snd e)) p hz
local notation "q" => cyclicHomNormalizedLocusPoint n pR hR

/-- The actual local atlas comparison reaches the direct original subgroup. -/
def localActualRelabeledIso :
    CompatibleIso ((normalizedSubgroup n false).baseChange q) (H.baseChange (k ≫ f)) :=
  (pointedCubicActualRelabeledIso W h₂ e J hQ).trans (d)

/-- This comparison retains the prescribed permutation of the original local frame. -/
theorem localActualRelabeledIso_auxiliary (i : Labels 4) :
    pullSection q (evenNormalizedAuxiliaryMarking n i) ≫
      (localActualRelabeledIso H f W h₂ J a e hQ).curve.hom.group =
        localOriginalAuxiliaryMarking H f W h₂ J a (e.1.symm i) := by
  exact CompatibleIso.group_section_trans (pointedCubicActualRelabeledIso W h₂ e J hQ)
    (d) _ _ _ (pointedCubicActualRelabeledIso_auxiliary W h₂ e J hQ i) rfl

/-- The same full comparison retains every prescribed relabeled generator power. -/
theorem localActualRelabeledIso_generator_pow {P : 𝟙_ (Over S) ⟶ H.carrier}
    (ha : Q ≫ a.subgroup.hom = pullSection f P) (m : ℕ) :
    (pullSection q (evenNormalizedGenerator n) ^ m) ≫
      (localActualRelabeledIso H f W h₂ J a e hQ).subgroup.hom =
        pullSection (k ≫ f) (P ^ (e.2.2.symm (.ofAdd (m : ZMod n))).toAdd.val) := by
  change _ ≫ ((pointedCubicActualRelabeledIso W h₂ e J hQ).subgroup.hom ≫
    (a.baseChange k).subgroup.hom ≫ (compatibleBaseChangeComp H f k).subgroup.inv) = _
  rw [← Category.assoc, pointedCubicActualRelabeledIso_generator_pow,
    ← Category.assoc]
  have hp (r : ℕ) : (Q ^ r) ≫ a.subgroup.hom = pullSection f (P ^ r) := by
    rw [pow_comp, ha, section_pow]
  rw [a.baseChange_section k _ _ (hp _)]
  exact compatibleBaseChangeComp_inv_section H f k _

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
