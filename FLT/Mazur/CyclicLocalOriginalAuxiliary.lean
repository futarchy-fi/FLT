/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicActualNormalizedAuxiliary
public import FLT.Mazur.CompatibleSubgroupAuxiliaryTransport

/-!
# Independent original auxiliary frames on local cubic neighborhoods

The original local cubic comparison transports its actual auxiliary cover
frame to the direct original family. The normalized atlas comparison then
retains this frame together with the independently prescribed generator.
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

/-- The local original frame uses only the cubic presentation and its actual auxiliary cover. -/
def localOriginalAuxiliaryMarking : Labels 4 →*
    (𝟙_ (Over (pointedCubicAuxiliaryCover W h₂).left) ⟶ (E.baseChange (k ≫ f)).group) :=
  (d).transportAuxiliary (pointedCubicOriginalAuxiliaryMarking W h₂)

/-- Faithfulness of the independent frame survives passage to the direct original family. -/
theorem localOriginalAuxiliaryMarking_injective
    [Nonempty (pointedCubicAuxiliaryCover W h₂).left] :
    Function.Injective (localOriginalAuxiliaryMarking H f W h₂ J a) :=
  ((d).transportAuxiliary_injective_iff _).mpr
    (pointedCubicOriginalAuxiliaryMarking_injective W h₂)

/-- The original neighborhood frame satisfies the full auxiliary torsion equations. -/
theorem localOriginalAuxiliaryMarking_pow (i : Labels 4) :
    localOriginalAuxiliaryMarking H f W h₂ J a i ^ 4 = 1 := by
  rw [← map_pow, labels_pow, map_one]

variable [NeZero n] {Q : 𝟙_ (Over T) ⟶ J.carrier} (hQ : J.IsCartierGenerator Q)
local notation "p" => Over.Hom.left (pointedCubicHomAuxiliaryParameter W h₂
  (J.generatorCurveMarking hQ))
local notation "hz" => pointedCubicHomPrescribed_equation W h₂ J hQ
local notation "q" => cyclicHomNormalizedLocusPoint n p hz

/-- The actual local atlas comparison reaches the direct original subgroup. -/
def localActualNormalizedIso :
    CompatibleIso ((normalizedSubgroup n false).baseChange q) (H.baseChange (k ≫ f)) :=
  (pointedCubicActualNormalizedIso W h₂ J hQ).trans (d)

/-- This comparison retains the independent original local auxiliary frame. -/
theorem localActualNormalizedIso_auxiliary (i : Labels 4) :
    pullSection q (evenNormalizedAuxiliaryMarking n i) ≫
      (localActualNormalizedIso H f W h₂ J a hQ).curve.hom.group =
        localOriginalAuxiliaryMarking H f W h₂ J a i := by
  exact CompatibleIso.group_section_trans (pointedCubicActualNormalizedIso W h₂ J hQ)
    (d) _ _ _ (pointedCubicActualNormalizedIso_auxiliary W h₂ J hQ i) rfl

/-- The same full comparison retains the prescribed original generator. -/
theorem localActualNormalizedIso_generator {P : 𝟙_ (Over S) ⟶ H.carrier}
    (ha : Q ≫ a.subgroup.hom = pullSection f P) :
    pullSection q (evenNormalizedGenerator n) ≫
      (localActualNormalizedIso H f W h₂ J a hQ).subgroup.hom =
        pullSection (k ≫ f) P := by
  change _ ≫ ((pointedCubicActualNormalizedIso W h₂ J hQ).subgroup.hom ≫
    (a.baseChange k).subgroup.hom ≫ (compatibleBaseChangeComp H f k).subgroup.inv) = _
  rw [← Category.assoc, pointedCubicActualNormalizedIso_generator,
    ← Category.assoc, a.baseChange_section k Q (pullSection f P) ha]
  exact compatibleBaseChangeComp_inv_section H f k P

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
