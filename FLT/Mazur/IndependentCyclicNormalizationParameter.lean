/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IndependentCyclicSourceMarking

/-!
# Normalization of independent cyclic parameters

Normalize the auxiliary point and transport the cyclic marking separately
through the actual normalization group isomorphism. Their images may intersect;
no product marking or coprimality hypothesis is introduced.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f : T ⟶ (independentCyclicAuxiliaryScheme n).left)
local notation "a" => independentCyclicAuxiliaryPoint n f
local notation "bN" => auxiliarySchemeNormalizedPoint a ≫ levelFour.hom

/-- The auxiliary normalization as a relative point over its actual normalized coefficients. -/
def independentCyclicNormalizedAuxiliary :
    (Over.map bN).obj (𝟙_ (Over T)) ⟶ levelFour :=
  Over.homMk (auxiliarySchemeNormalizedPoint a) (Category.id_comp _).symm

/-- The entire independent parameter over the normalized coefficient map. -/
def independentCyclicNormalizedParameter :
    (Over.map bN).obj (𝟙_ (Over T)) ⟶ independentCyclicAuxiliaryScheme n :=
  independentCyclicLift n (independentCyclicNormalizedAuxiliary n f)
    (auxiliarySchemeFullNormalizedParameter a (Multiplicative (ZMod n))
      (independentCyclicGroupPoint n f))

/-- The actual normalized independent point on the original test scheme. -/
def independentCyclicNormalizedPoint : T ⟶ (independentCyclicAuxiliaryScheme n).left :=
  (independentCyclicNormalizedParameter n f).left

/-- Normalization retains the previously constructed auxiliary normalization exactly. -/
@[reassoc] theorem independentCyclicNormalizedPoint_auxiliary :
    independentCyclicNormalizedPoint n f ≫ (independentCyclicAuxiliary n).left =
      auxiliarySchemeNormalizedPoint a :=
  congrArg Over.Hom.left (independentCyclicLift_auxiliary n _ _)

/-- The cyclic factor is transported through the established normalization comparison. -/
@[reassoc] theorem independentCyclicNormalizedPoint_cyclic :
    independentCyclicNormalizedPoint n f ≫ (independentCyclicParameter n).left =
      (auxiliarySchemeFullNormalizedParameter a (Multiplicative (ZMod n))
        (independentCyclicGroupPoint n f)).left :=
  congrArg Over.Hom.left (independentCyclicLift_cyclic n _ _)

/-- The normalized point uses exactly the normalized auxiliary coefficient map. -/
@[reassoc] theorem independentCyclicNormalizedPoint_base :
    independentCyclicNormalizedPoint n f ≫ (independentCyclicAuxiliaryScheme n).hom = bN :=
  (independentCyclicNormalizedParameter n f).w.trans (Category.id_comp _)

/-- Every cyclic label retains its original section through the normalization group isomorphism. -/
theorem independentCyclicNormalizedPoint_value (c : Multiplicative (ZMod n)) :
    independentCyclicNormalizedPoint n f ≫ (independentCyclicParameter n ≫
      faithfulInclusion universalGroup (Multiplicative (ZMod n)) ≫
        value universalGroup (Multiplicative (ZMod n)) c).left =
      (independentCyclicSourceMarking n f c).left ≫
        (auxiliarySchemeNormalizationGroupIso a).inv.hom.hom.hom.left ≫
          pullback.fst universalGroup.hom bN := by
  rw [Over.comp_left, ← Category.assoc, independentCyclicNormalizedPoint_cyclic]
  exact auxiliarySchemeFullNormalizedParameter_value a (Multiplicative (ZMod n))
    (independentCyclicGroupPoint n f) c

end FLT.Mazur.UniversalWeierstrass
