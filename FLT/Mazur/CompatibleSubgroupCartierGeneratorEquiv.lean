/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupIso

/-!
# All Cartier generators under compatible subgroup comparisons

A full compatible comparison transports every Cartier generator bijectively.
The inverse uses the actual inverse subgroup map, including at non-etale levels.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {n : ℕ} {E F : GeneralizedEllipticCurve S}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}

/-- A compatible comparison bijects all Cartier generators of the full subgroup schemes. -/
def compatibleCartierGeneratorEquiv (a : CompatibleIso H J) :
    {P : 𝟙_ (Over S) ⟶ H.carrier // H.IsCartierGenerator P} ≃
      {Q : 𝟙_ (Over S) ⟶ J.carrier // J.IsCartierGenerator Q} where
  toFun P := ⟨P.val ≫ a.subgroup.hom, a.cartierGenerator P.property⟩
  invFun Q := ⟨Q.val ≫ a.subgroup.inv, a.symm.cartierGenerator Q.property⟩
  left_inv P := Subtype.ext (by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])
  right_inv Q := Subtype.ext (by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The generator equivalence uses the unchanged subgroup inclusion square. -/
theorem compatibleCartierGeneratorEquiv_curve (a : CompatibleIso H J)
    (P : {P : 𝟙_ (Over S) ⟶ H.carrier // H.IsCartierGenerator P}) :
    (compatibleCartierGeneratorEquiv a P).val ≫ J.curveMap =
      P.val ≫ H.curveMap ≫ a.curve.hom.curve := by
  change (P.val ≫ a.subgroup.hom) ≫ J.curveMap = _
  rw [Category.assoc, ← a.compatible]

/-- Every target Cartier generator has a unique original generator under the full comparison. -/
theorem compatibleCartierGeneratorEquiv_unique (a : CompatibleIso H J)
    (Q : {Q : 𝟙_ (Over S) ⟶ J.carrier // J.IsCartierGenerator Q}) :
    ∃! P : {P : 𝟙_ (Over S) ⟶ H.carrier // H.IsCartierGenerator P},
      compatibleCartierGeneratorEquiv a P = Q :=
  (compatibleCartierGeneratorEquiv a).bijective.existsUnique Q

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
