/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicOriginalMarking

/-!
# The full cyclic marking on the actual normalized source group

Transport through the actual normalization isomorphism retains both factors,
faithfulness, and the exact order of the cyclic generator. The auxiliary
factor agrees with the previously constructed normalized auxiliary marking.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open AuxiliaryLevel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme} (f : T ⟶ (cyclicAuxiliaryScheme n).left)
local notation "aO" => cyclicSchemeAuxiliaryPoint n f
local notation "aN" => auxiliarySchemeNormalizedPoint aO
local notation "e" => auxiliarySchemeNormalizationGroupIso aO

/-- The entire original cyclic marking on the actual normalized group family. -/
def cyclicSchemeNormalizedMarking :
    CyclicLabels n →* (𝟙_ (Over T) ⟶ (auxiliarySchemeGroup aN).X) :=
  GroupMarkingTransport.transport (auxiliarySchemeGroup aO) (auxiliarySchemeGroup aN)
    (e).symm (cyclicSchemeOriginalMarking n f)

/-- The actual normalization comparison recovers every original label. -/
@[reassoc] theorem cyclicSchemeNormalizedMarking_compare (c : CyclicLabels n) :
    cyclicSchemeNormalizedMarking n f c ≫ (e).hom.hom.hom.hom =
      cyclicSchemeOriginalMarking n f c := by
  change (cyclicSchemeOriginalMarking n f c ≫ (e).inv.hom.hom.hom) ≫ _ = _
  have hi : (e).inv.hom.hom.hom ≫ (e).hom.hom.hom.hom = 𝟙 _ :=
    congrArg (fun k ↦ k.hom.hom.hom) (e).inv_hom_id
  rw [Category.assoc, hi, Category.comp_id]

/-- Its auxiliary factor is exactly the already constructed normalized auxiliary marking. -/
theorem cyclicSchemeNormalizedMarking_auxiliary (c : Labels 4) :
    cyclicSchemeNormalizedMarking n f (c, 1) = auxiliarySchemeMarking aN c := by
  apply (cancel_mono (auxiliarySchemeNormalizationOverIso aO).hom).mp
  change _ ≫ (e).hom.hom.hom.hom = _ ≫ (e).hom.hom.hom.hom
  rw [cyclicSchemeNormalizedMarking_compare, auxiliarySchemeNormalizationGroupIso_marking,
    cyclicSchemeOriginalMarking_auxiliary]

/-- Projection of every normalized label is its actual new universal parameter value. -/
@[reassoc] theorem cyclicSchemeNormalizedMarking_fst (c : CyclicLabels n) :
    (cyclicSchemeNormalizedMarking n f c).left ≫
      pullback.fst universalGroup.hom (aN ≫ levelFour.hom) =
        cyclicSchemeNormalizedPoint n f ≫
          (cyclicAuxiliaryInclusion n ≫ value universalGroup (CyclicLabels n) c).left := by
  rw [cyclicSchemeNormalizedPoint_value]
  change (cyclicSchemeOriginalMarking n f c ≫ (e).inv.hom.hom.hom).left ≫ _ = _
  rw [Over.comp_left, Category.assoc]
  rfl

/-- Both original label factors retain faithfulness after normalization. -/
theorem cyclicSchemeNormalizedMarking_injective [Nonempty T] :
    Function.Injective (cyclicSchemeNormalizedMarking n f) :=
  (GroupMarkingTransport.transport_injective_iff _ _ _ _).mpr
    (cyclicSchemeOriginalMarking_injective n f)

/-- The cyclic generator retains exact order after actual normalization. -/
theorem cyclicSchemeNormalizedMarking_order [Nonempty T] :
    orderOf (cyclicSchemeNormalizedMarking n f (cyclicLabel n)) = n :=
  (orderOf_injective _ (cyclicSchemeNormalizedMarking_injective n f) (cyclicLabel n)).trans
    (cyclicLabel_order n)

/-- Every full label splits into its retained auxiliary and cyclic factors. -/
theorem cyclicSchemeNormalizedMarking_factors (c : Labels 4) (d : Multiplicative (ZMod n)) :
    cyclicSchemeNormalizedMarking n f (c, d) =
      auxiliarySchemeMarking aN c * cyclicSchemeNormalizedMarking n f (1, d) := by
  have h := (cyclicSchemeNormalizedMarking n f).map_mul (c, 1) (1, d)
  rw [Prod.mk_mul_mk, _root_.mul_one, _root_.one_mul,
    cyclicSchemeNormalizedMarking_auxiliary] at h
  exact h

end FLT.Mazur.UniversalWeierstrass
