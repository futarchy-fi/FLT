/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleFrameComparisonUnit

/-!
# A regular section determines frame coordinates

Two specified frames agreeing on a section with regular coordinate agree
on every section. The argument cancels the actual coordinate; it does not
require that section to generate the module.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {M : X.Modules}
variable (e f : M ≅ structureModule X) (U : X.Opens)

/-- A shared regular coordinate forces the exact frame comparison scalar to be one. -/
theorem frameComparisonUnit_eq_one_of_regular (c : Γ(M, U))
    (hr : IsRegular (show Γ(X, U) from f.hom.app U c))
    (hc : e.hom.app U c = f.hom.app U c) :
    frameComparisonUnit e f U = 1 := by
  apply Units.ext
  apply hr.right
  have he := frameComparisonUnit_apply e f U c
  rw [hc] at he
  exact he.symm.trans (one_mul (show Γ(X, U) from f.hom.app U c)).symm

/-- Agreement on one regular section determines the coordinates of every retained section. -/
theorem frame_apply_eq_of_regular (c : Γ(M, U))
    (hr : IsRegular (show Γ(X, U) from f.hom.app U c))
    (hc : e.hom.app U c = f.hom.app U c) (s : Γ(M, U)) :
    e.hom.app U s = f.hom.app U s := by
  rw [frameComparisonUnit_apply, frameComparisonUnit_eq_one_of_regular e f U c hr hc,
    Units.val_one, one_mul]

end FLT.Mazur.FCurve
