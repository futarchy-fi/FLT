/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupIso

/-!
# The whole curve determines compatible subgroup comparisons

The original subgroup inclusion is monomorphic. Consequently a prescribed
full curve isomorphism admits at most one compatible subgroup isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {n : ℕ} {E F : GeneralizedEllipticCurve S}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}

/-- Compatible subgroup maps are determined by their full curve maps. -/
theorem CompatibleIso.subgroup_hom_eq (a b : CompatibleIso H J)
    (hc : a.curve.hom = b.curve.hom) : a.subgroup.hom = b.subgroup.hom := by
  let _ : Mono J.curveMap := Over.mono_of_mono_left _
  apply (cancel_mono J.curveMap).mp
  rw [← a.compatible, ← b.compatible, hc]

/-- Forgetting a compatible comparison to its full curve is faithful. -/
theorem CompatibleIso.ext_curve {a b : CompatibleIso H J}
    (hc : a.curve = b.curve) : a = b := by
  apply CompatibleIso.ext H J hc
  apply Iso.ext
  exact a.subgroup_hom_eq b (congrArg Iso.hom hc)

/-- Equality of the underlying full curve maps detects equality of comparisons. -/
theorem CompatibleIso.ext_curve_hom {a b : CompatibleIso H J}
    (hc : a.curve.hom = b.curve.hom) : a = b :=
  CompatibleIso.ext_curve (Iso.ext hc)

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
