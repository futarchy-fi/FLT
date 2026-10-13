/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierGeneratorMarkedSubgroup

/-!
# Full compatible comparisons preserve Cartier generator markings

This comparison uses the original subgroup inclusion and powers of its actual
generator. It requires neither distinct sections nor etale subgroup schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {E F : GeneralizedEllipticCurve S} {n : ℕ}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n} (a : CompatibleIso H J)

/-- Compatibility on the whole curve restricts to the original smooth group inclusions. -/
@[reassoc] theorem CompatibleIso.group_inclusion :
    H.inclusion ≫ a.curve.hom.group = a.subgroup.hom ≫ J.inclusion := by
  let _ : Mono F.inclusion := Over.mono_of_mono_left F.inclusion
  apply (cancel_mono F.inclusion).mp
  rw [Category.assoc, ← a.curve.hom.inclusion, ← Category.assoc, Category.assoc]
  exact a.compatible

variable [NeZero n] {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)

/-- Every cyclic label is carried by the specified full comparison. -/
theorem CompatibleIso.generatorCurveMarking (i : Multiplicative (ZMod n)) :
    J.generatorCurveMarking (a.cartierGenerator hP) i =
      H.generatorCurveMarking hP i ≫ a.curve.hom.group := by
  change ((P ≫ a.subgroup.hom) ^ i.toAdd.val) ≫ J.inclusion =
    ((P ^ i.toAdd.val) ≫ H.inclusion) ≫ a.curve.hom.group
  rw [← pow_comp, Category.assoc, Category.assoc, a.group_inclusion]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
