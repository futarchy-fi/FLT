/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicNaturalGroup

/-!
# Source change of the original full cyclic group family

The comparison between iterated and direct pullback retains the original
coefficient map and the universal family projection.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f : T ⟶ (cyclicAuxiliaryScheme n).left) (k : U ⟶ T)
local notation "a" => cyclicSchemeAuxiliaryPoint n f
local notation "b" => cyclicSchemeAuxiliaryPoint n (k ≫ f)
local notation "G" => integralCurveGroup smoothEquation smoothEquation_discriminant

/-- The two constructions use exactly the same original coefficient map. -/
theorem cyclicSourceOriginalGroup_base :
    k ≫ (a ≫ levelFour.hom) = b ≫ levelFour.hom := by
  simp only [cyclicSchemeAuxiliaryPoint, Category.assoc]

/-- Pulling back an original family gives the original family at the pulled-back full point. -/
irreducible_def cyclicSourceOriginalGroupIso :
    (Over.pullback k).mapCommGrp.obj (auxiliarySchemeGroup a) ≅ auxiliarySchemeGroup b :=
  (GroupSchemeBaseChange.compIso k (a ≫ levelFour.hom) G).symm ≪≫
    GroupSchemeBaseChange.congrIso (cyclicSourceOriginalGroup_base n f k) G

/-- The source comparison retains the exact universal projection. -/
@[reassoc] theorem cyclicSourceOriginalGroupIso_fst :
    (cyclicSourceOriginalGroupIso n f k).hom.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom (b ≫ levelFour.hom) =
        pullback.fst (auxiliarySchemeGroup a).X.hom k ≫
          pullback.fst universalGroup.hom (a ≫ levelFour.hom) := by
  rw [cyclicSourceOriginalGroupIso_def]
  change (_ ≫ _) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦
      (GroupSchemeBaseChange.compIso k (a ≫ levelFour.hom) G).inv.hom.hom.hom.left ≫ z)
        (GroupSchemeBaseChange.congrIso_hom_fst (cyclicSourceOriginalGroup_base n f k) G)).trans
          (GroupSchemeBaseChange.compIso_inv_fst k (a ≫ levelFour.hom) G))

end FLT.Mazur.UniversalWeierstrass
