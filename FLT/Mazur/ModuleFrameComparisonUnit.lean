/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionMap

/-!
# The exact unit comparing two retained module frames

Two frames of the same module differ by the value of one on the inverse
unit section of the other. This constructs that unit and its inverse;
it does not identify the two frames or normalize any retained section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {M : X.Modules}
variable (e f : M ≅ structureModule X) (U : X.Opens)

/-- The original section is its scalar coordinate times the original inverse unit section. -/
theorem frame_section_eq_smul (s : Γ(M, U)) :
    s = (show Γ(X, U) from e.hom.app U s) • e.inv.app U (1 : Γ(X, U)) := by
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app U)).injective
  rw [Hom.app_smul, sectionIso_hom_inv, smul_eq_mul, mul_one]

/-- The exact coordinate change keeps both specified frames. -/
theorem frame_comparison_apply (s : Γ(M, U)) :
    e.hom.app U s =
      (show Γ(X, U) from e.hom.app U (f.inv.app U (1 : Γ(X, U)))) *
        (show Γ(X, U) from f.hom.app U s) := by
  conv_lhs => rw [frame_section_eq_smul f U s]
  rw [Hom.app_smul, smul_eq_mul, mul_comm]

/-- The forward comparison scalar and the reverse comparison scalar are inverse. -/
theorem frame_comparison_mul_inverse :
    (show Γ(X, U) from e.hom.app U (f.inv.app U (1 : Γ(X, U)))) *
      (show Γ(X, U) from f.hom.app U (e.inv.app U (1 : Γ(X, U)))) = 1 := by
  rw [← frame_comparison_apply, sectionIso_hom_inv]

/-- The actual transition unit between two frames of the same original module. -/
def frameComparisonUnit : Γ(X, U)ˣ where
  val := e.hom.app U (f.inv.app U (1 : Γ(X, U)))
  inv := f.hom.app U (e.inv.app U (1 : Γ(X, U)))
  val_inv := frame_comparison_mul_inverse e f U
  inv_val := frame_comparison_mul_inverse f e U

/-- The constructed transition unit gives the full coefficient change. -/
theorem frameComparisonUnit_apply (s : Γ(M, U)) :
    e.hom.app U s = (frameComparisonUnit e f U : Γ(X, U)) * (show Γ(X, U) from f.hom.app U s) :=
  frame_comparison_apply e f U s

/-- A section normalized in the retained frame has the transition unit in the other frame. -/
theorem frameComparisonUnit_of_coefficient_one (s : Γ(M, U))
    (hs : f.hom.app U s = (1 : Γ(X, U))) :
    e.hom.app U s = (frameComparisonUnit e f U : Γ(X, U)) := by
  rw [frameComparisonUnit_apply e f U s, hs, mul_one]

end FLT.Mazur.FCurve
