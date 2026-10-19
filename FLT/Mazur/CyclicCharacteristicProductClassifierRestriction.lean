/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductCompatibleClassification
public import FLT.Mazur.CyclicCharacteristicProductTestRestriction

/-!
# Naturality of the compatible comparison classifier

The inverse classifier commutes with arbitrary scheme maps. Its value is an
actual parameter map, retaining the specified compatible isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool) {T V : Scheme}
  (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c)
local notation "ss" => productSubgroupStructure n b c

/-- The actual parameter classifying a specified compatible comparison. -/
def productCompatibleParameter
    (a : CompatibleIso ((normalizedSubgroup n b).baseChange q)
      ((normalizedSubgroup n c).baseChange r)) :
    {k : T ⟶ productSubgroupScheme n b c // k ≫ ss = prod.lift q r} :=
  (productCompatibleSchemePointEquiv n b c q r).symm a

/-- Evaluation recovers the entire specified compatible comparison. -/
theorem productCompatibleParameter_recovers
    (a : CompatibleIso ((normalizedSubgroup n b).baseChange q)
      ((normalizedSubgroup n c).baseChange r)) :
    productCompatibleTestComparison n b c q r (productCompatibleParameter n b c q r a) =
      a := (productCompatibleSchemePointEquiv n b c q r).apply_symm_apply a

/-- Parameter evaluation commutes with restriction to any scheme test. -/
theorem productCompatibleTestComparison_restrict (l : V ⟶ T)
    (k : {k : T ⟶ productSubgroupScheme n b c // k ≫ ss = prod.lift q r}) :
    (compatibleBaseChangeCompEq (normalizedSubgroup n b) q l (l ≫ q) rfl).trans
        (((productCompatibleTestComparison n b c q r k).baseChange l).trans
          (compatibleBaseChangeCompEq (normalizedSubgroup n c) r l (l ≫ r) rfl).symm) =
      productCompatibleTestComparison n b c (l ≫ q) (l ≫ r)
        ⟨l ≫ k.val, by rw [Category.assoc, k.property, prod.comp_lift]⟩ :=
  productUniversalSubgroupComparisonOnTest_restrict n b c l q r (l ≫ q) (l ≫ r)
    rfl rfl k.val _ _

/-- Restricting a comparison precomposes its unique classifying scheme map. -/
theorem productCompatibleParameter_restrict (l : V ⟶ T)
    (a : CompatibleIso ((normalizedSubgroup n b).baseChange q)
      ((normalizedSubgroup n c).baseChange r)) :
    (productCompatibleParameter n b c (l ≫ q) (l ≫ r)
      ((compatibleBaseChangeCompEq (normalizedSubgroup n b) q l (l ≫ q) rfl).trans
        ((a.baseChange l).trans
          (compatibleBaseChangeCompEq (normalizedSubgroup n c) r l (l ≫ r) rfl).symm))).val =
      l ≫ (productCompatibleParameter n b c q r a).val := by
  let k := productCompatibleParameter n b c q r a
  have h := productCompatibleTestComparison_restrict n b c q r l k
  rw [productCompatibleParameter_recovers] at h
  have he := (productCompatibleSchemePointEquiv n b c (l ≫ q) (l ≫ r)).injective
    ((productCompatibleParameter_recovers n b c (l ≫ q) (l ≫ r) _).trans h)
  exact congrArg Subtype.val he

end FLT.Mazur.CyclicCharacteristicAtlas
