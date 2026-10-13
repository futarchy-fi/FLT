/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomRelabelCurve
public import FLT.Mazur.UniversalWeierstrassAuxiliaryRelabelCoordinates

/-!
# Relabeling retains the independent auxiliary marking on the full source family

The same full comparison that retains every cyclic section also carries all
auxiliary labels with their prescribed inverse permutation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (a : MulAut (Labels 4)) (c : MulAut (Multiplicative (ZMod n)))
  {T : Scheme} (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
local notation "fR" => f ≫ Over.Hom.left (cyclicHomRelabel n a c)

/-- The auxiliary point of the actual relabeled parameter is its original auxiliary action. -/
theorem cyclicHomRelabel_auxiliaryPoint :
    cyclicHomAuxiliaryPoint n fR =
      cyclicHomAuxiliaryPoint n f ≫ (auxiliaryAction 4 a).hom := by
  have h := congrArg (fun z ↦ f ≫ z.left) (cyclicHomRelabel_auxiliary n a c)
  exact (Category.assoc _ _ _).trans h

/-- The full curve comparison retains every independent auxiliary label. -/
theorem cyclicHomRelabelCurveIso_auxiliary (i : Labels 4) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n fR) i ≫
      (cyclicHomRelabelCurveIso n a c f).hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) (a.symm i) := by
  apply auxiliarySchemeMarking_ext
  rw [Over.comp_left, Category.assoc, cyclicHomRelabelCurveIso_fst,
    auxiliarySchemeMarking_fst, cyclicHomRelabel_auxiliaryPoint, Category.assoc]
  exact congrArg (fun z ↦ cyclicHomAuxiliaryPoint n f ≫ z)
    (auxiliaryAction_mark a i)

end FLT.Mazur.UniversalWeierstrass
