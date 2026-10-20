/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupIso

/-!
# Smoothness is invariant under compatible full-curve comparisons

The comparison retains the entire relative curve, so smoothness of that
curve is preserved. This distinguishes smooth parameters from boundary levels.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {n : ℕ} {E F : GeneralizedEllipticCurve S}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}

/-- Compatible subgroup comparisons preserve smoothness of the whole relative curve. -/
theorem CompatibleIso.smooth_iff (a : CompatibleIso H J) :
    Smooth E.curve.hom ↔ Smooth F.curve.hom := by
  let e := curveIso a.curve
  constructor
  · intro h
    let _ := h
    have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget S).map e.inv))
    rw [← e.inv.w]
    infer_instance
  · intro h
    let _ := h
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
    rw [← e.hom.w]
    infer_instance

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
