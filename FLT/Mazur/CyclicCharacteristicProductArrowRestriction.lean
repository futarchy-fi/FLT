/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductParameterGroupoid

/-!
# Restriction of actual ordered-pair arrows

Restriction allows prescribed endpoint maps, so the universal scheme operations
can be tested without replacing the original families by iterated pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T V : Scheme} {b c d : Bool}
  {q : T ⟶ normalizedLocus n b} {r : T ⟶ normalizedLocus n c}
  {s : T ⟶ normalizedLocus n d}
  (l : V ⟶ T) (v : V ⟶ normalizedLocus n b) (w : V ⟶ normalizedLocus n c)
  (hv : v = l ≫ q) (hw : w = l ≫ r)

/-- Precomposition of a parameter, retaining prescribed endpoint maps. -/
def productArrowRestrict (a : ProductArrow n q r) : ProductArrow n v w :=
  ⟨l ≫ a.val, by rw [Category.assoc, a.property, prod.comp_lift, hv, hw]⟩

/-- Evaluation of restriction is the compatible pullback of the specified comparison. -/
theorem productArrowRestrict_eval (a : ProductArrow n q r) :
    productCompatibleTestComparison n b c v w (productArrowRestrict n l v w hv hw a) =
      (compatibleBaseChangeCompEq (normalizedSubgroup n b) q l v hv).trans
        (((productCompatibleTestComparison n b c q r a).baseChange l).trans
          (compatibleBaseChangeCompEq (normalizedSubgroup n c) r l w hw).symm) := by
  exact (productUniversalSubgroupComparisonOnTest_restrict n b c l q r v w hv hw
    a.val _ _).symm

include hv in
/-- Restriction preserves identity parameters. -/
theorem productArrowRestrict_id :
    productArrowRestrict n l v v hv hv (productArrowId n q) = productArrowId n v := by
  apply productArrow_ext n
  rw [productArrowRestrict_eval, productArrowId_eval, productArrowId_eval,
    CompatibleIso.baseChange_refl, CompatibleIso.refl_trans, CompatibleIso.trans_symm]

/-- Restriction preserves inverse parameters. -/
theorem productArrowRestrict_inv (a : ProductArrow n q r) :
    productArrowRestrict n l w v hw hv (productArrowInv n a) =
      productArrowInv n (productArrowRestrict n l v w hv hw a) := by
  apply productArrow_ext n
  rw [productArrowRestrict_eval, productArrowInv_eval, productArrowInv_eval,
    productArrowRestrict_eval]
  apply CompatibleIso.ext_curve
  simp [CompatibleIso.trans, CompatibleIso.symm, CompatibleIso.baseChange]

/-- Restriction preserves composition parameters with the same prescribed middle endpoint. -/
theorem productArrowRestrict_comp (u : V ⟶ normalizedLocus n d) (hu : u = l ≫ s)
    (a : ProductArrow n q r) (z : ProductArrow n r s) :
    productArrowRestrict n l v u hv hu (productArrowComp n a z) =
      productArrowComp n (productArrowRestrict n l v w hv hw a)
        (productArrowRestrict n l w u hw hu z) := by
  apply productArrow_ext n
  rw [productArrowRestrict_eval, productArrowComp_eval, productArrowComp_eval,
    productArrowRestrict_eval, productArrowRestrict_eval, CompatibleIso.baseChange_trans]
  apply CompatibleIso.ext_curve
  simp [CompatibleIso.trans, CompatibleIso.symm]

end FLT.Mazur.CyclicCharacteristicAtlas
