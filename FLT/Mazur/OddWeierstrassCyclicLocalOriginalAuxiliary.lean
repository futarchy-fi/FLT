/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassPointedCubicActualNormalizedAuxiliary
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
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
open CyclicCharacteristicAtlas GroupSectionBaseChange
open UniversalWeierstrass (Labels labels_pow)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ}
  (H : E.FiniteSubgroup n) (f : T ⟶ S)
  (W : WeierstrassCurve Γ(T, ⊤)) [W.IsElliptic] (h₃ : IsUnit (3 : Γ(T, ⊤)))
  (J : (pointedCubicFamily W).FiniteSubgroup n) (a : CompatibleIso J (H.baseChange f))
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₃)
local notation "d" => CompatibleIso.trans (CompatibleIso.baseChange a k)
  (CompatibleIso.symm (compatibleBaseChangeComp H f k))

/-- The local original frame uses only the cubic presentation and its actual auxiliary cover. -/
def localOriginalAuxiliaryMarking : Labels 3 →*
    (𝟙_ (Over (pointedCubicAuxiliaryCover W h₃).left) ⟶ (E.baseChange (k ≫ f)).group) :=
  (d).transportAuxiliary (pointedCubicOriginalAuxiliaryMarking W h₃)

/-- Faithfulness of the independent frame survives passage to the direct original family. -/
theorem localOriginalAuxiliaryMarking_injective
    [Nonempty (pointedCubicAuxiliaryCover W h₃).left] :
    Function.Injective (localOriginalAuxiliaryMarking H f W h₃ J a) :=
  ((d).transportAuxiliary_injective_iff _).mpr
    (pointedCubicOriginalAuxiliaryMarking_injective W h₃)

/-- The original neighborhood frame satisfies the full auxiliary torsion equations. -/
theorem localOriginalAuxiliaryMarking_pow (i : Labels 3) :
    localOriginalAuxiliaryMarking H f W h₃ J a i ^ 3 = 1 := by
  rw [← map_pow, labels_pow, map_one]

variable [NeZero n] {Q : 𝟙_ (Over T) ⟶ J.carrier} (hQ : J.IsCartierGenerator Q)
local notation "p" => Over.Hom.left (pointedCubicHomAuxiliaryParameter W h₃
  (J.generatorCurveMarking hQ))
local notation "hz" => pointedCubicHomPrescribed_equation W h₃ J hQ
local notation "q" => cyclicHomNormalizedLocusPoint n p hz

/-- The actual local atlas comparison reaches the direct original subgroup. -/
def localActualNormalizedIso :
    CompatibleIso ((normalizedSubgroup n true).baseChange q) (H.baseChange (k ≫ f)) :=
  (pointedCubicActualNormalizedIso W h₃ J hQ).trans (d)

/-- This comparison retains the independent original local auxiliary frame. -/
theorem localActualNormalizedIso_auxiliary (i : Labels 3) :
    pullSection q (oddNormalizedAuxiliaryMarking n i) ≫
      (localActualNormalizedIso H f W h₃ J a hQ).curve.hom.group =
        localOriginalAuxiliaryMarking H f W h₃ J a i := by
  exact CompatibleIso.group_section_trans (pointedCubicActualNormalizedIso W h₃ J hQ)
    (d) _ _ _ (pointedCubicActualNormalizedIso_auxiliary W h₃ J hQ i) rfl

/-- The same full comparison retains the prescribed original generator. -/
theorem localActualNormalizedIso_generator {P : 𝟙_ (Over S) ⟶ H.carrier}
    (ha : Q ≫ a.subgroup.hom = pullSection f P) :
    pullSection q (oddNormalizedGenerator n) ≫
      (localActualNormalizedIso H f W h₃ J a hQ).subgroup.hom =
        pullSection (k ≫ f) P := by
  change _ ≫ ((pointedCubicActualNormalizedIso W h₃ J hQ).subgroup.hom ≫
    (a.baseChange k).subgroup.hom ≫ (compatibleBaseChangeComp H f k).subgroup.inv) = _
  rw [← Category.assoc, pointedCubicActualNormalizedIso_generator,
    ← Category.assoc, a.baseChange_section k Q (pullSection f P) ha]
  exact compatibleBaseChangeComp_inv_section H f k P

end FLT.Mazur.OddWeierstrassParameter
