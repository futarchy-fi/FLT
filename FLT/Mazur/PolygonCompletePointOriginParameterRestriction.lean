/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointOriginParameter

/-!
# Restricting the actual parameter to original source opens

The pulled parameter becomes the original X/Y ratio on every smaller source open.
The original structure-sheaf restriction and open-subscheme comparison are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)
local notation "L" => divisorLineBundle (Scheme.Hom.ker (s)) hI
local notation "T" => completePointProjectiveSections K n h i
local notation "U" => sectionGeneratorOpen (tensorPower (L) 3) (T 1)
local notation "V" => completePointOriginOpen K n h i
local notation "g" => completePointToIntegralCubic K n h i

/-- The original parameter in the ambient section ring of its actual inverse image. -/
theorem completePointToOrigin_parameter_ambient :
    (V).topIso.hom ((completePointToOrigin K n h i).appTop
      (originParameterSection (W))) =
        sectionRatioOn (tensorPower (L) 3) (T 1) (V)
          (completePointOriginOpen_le_y K n h i) (T 0) := by
  rw [completePointToOrigin_parameter]
  change (V).topIso.hom (((exactVeroneseProj K n h).homOfLE
    (completePointOriginOpen_le_y K n h i)).appTop _) = _
  rw [homOfLE_topIso_inv, Iso.inv_hom_id_apply, sectionRatioOn_restrict]

/-- On every smaller original open, the parameter retains the actual normalized ratio. -/
theorem completePointToOrigin_parameter_restrict (A : (exactVeroneseProj K n h).Opens)
    (hA : A ≤ (V)) :
    (exactVeroneseProj K n h).presheaf.map (homOfLE hA).op
      ((V).topIso.hom ((completePointToOrigin K n h i).appTop
        (originParameterSection (W)))) =
      sectionRatioOn (tensorPower (L) 3) (T 1) A
        (hA.trans (completePointOriginOpen_le_y K n h i)) (T 0) := by
  rw [completePointToOrigin_parameter_ambient, sectionRatioOn_restrict]

/-- The genuine map from each smaller source open gives the same parameter coordinate. -/
theorem completePointToOrigin_parameter_subopen (A : (exactVeroneseProj K n h).Opens)
    (hA : A ≤ (V)) :
    (((exactVeroneseProj K n h).homOfLE hA) ≫
      completePointToOrigin K n h i).appTop (originParameterSection (W)) =
        A.topIso.inv (sectionRatioOn (tensorPower (L) 3) (T 1) A
          (hA.trans (completePointOriginOpen_le_y K n h i)) (T 0)) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have he := completePointToOrigin_parameter_ambient K n h i
  have hp := congrArg (fun a => (V).topIso.inv a) he
  rw [Iso.hom_inv_id_apply] at hp
  rw [hp, homOfLE_topIso_inv, sectionRatioOn_restrict]

end FLT.Mazur.PolygonInfinitesimalStages
