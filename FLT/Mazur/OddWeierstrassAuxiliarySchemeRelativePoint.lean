/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassNormalizedMarking

/-!
# Odd characteristic chart: the actual relative auxiliary point of an arbitrary scheme family

Global coefficient functions place any actual auxiliary family over the
spectrum of its own global sections. The original scheme morphism remains
the relative point; no morphism to the auxiliary scheme is inferred from
its global functions alone.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OddWeierstrassParameter
open IntegralWeierstrassParameter (OddChartRing oddChartEquation oddChart_discriminant)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {T : Scheme} (f : T ⟶ levelThree.left)

/-- The actual coefficient parameter of a scheme family is obtained from its global functions. -/
theorem auxiliarySchemeSections_base :
    T.toSpecΓ ≫ auxiliaryCoefficientBase f.appTop.hom = f ≫ levelThree.hom := by
  change T.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of OddChartRing)).inv ≫
    levelThree.hom.appTop ≫ f.appTop) = _
  rw [← Scheme.Hom.comp_appTop, Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc]
  change (f ≫ levelThree.hom) ≫ (Spec (.of OddChartRing)).toSpecΓ ≫
    Spec.map (Scheme.ΓSpecIso (.of OddChartRing)).inv = _
  rw [toSpecΓ_SpecMap_ΓSpecIso_inv]
  exact Category.comp_id _

/-- The original test scheme viewed over the spectrum of its global sections. -/
def auxiliarySchemeTest : Over (Spec (.of Γ(T, ⊤))) := Over.mk T.toSpecΓ

/-- The original scheme family is an actual relative auxiliary point over its coefficients. -/
def auxiliarySchemeRelativePoint :
    (Over.map (auxiliaryCoefficientBase f.appTop.hom)).obj (auxiliarySchemeTest (T := T)) ⟶
      levelThree :=
  Over.homMk f (auxiliarySchemeSections_base f).symm

/-- The relative point retains the entire original scheme morphism. -/
theorem auxiliarySchemeRelativePoint_left : (auxiliarySchemeRelativePoint f).left = f := rfl

/-- Every actual scheme family has an actual normalized level-three point. -/
def auxiliarySchemeNormalizedPoint : T ⟶ levelThree.left :=
  (auxiliaryNormalizedLevelPoint f.appTop.hom (auxiliarySchemeRelativePoint f)).left

/-- Its coefficient parameter is the original normalized parameter over global sections. -/
@[reassoc] theorem auxiliarySchemeNormalizedPoint_base :
    auxiliarySchemeNormalizedPoint f ≫ levelThree.hom =
      T.toSpecΓ ≫ auxiliaryNormalizedCoefficientBase f.appTop.hom :=
  (auxiliaryNormalizedLevelPoint f.appTop.hom (auxiliarySchemeRelativePoint f)).w

end FLT.Mazur.OddWeierstrassParameter
