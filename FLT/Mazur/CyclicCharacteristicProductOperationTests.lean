/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductCompositionScheme
public import FLT.Mazur.CyclicCharacteristicProductArrowRestriction

/-!
# Scheme operations recover the operations on every test

The identity, inverse, and composition morphisms induce exactly the operations
on specified compatible comparisons on every scheme test.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme} {b c d : Bool}
  {q : T ⟶ normalizedLocus n b} {r : T ⟶ normalizedLocus n c}
  {s : T ⟶ normalizedLocus n d}

/-- Every parameter is restriction of the tautological arrow with its original endpoints. -/
theorem productUniversalArrow_restrict (a : ProductArrow n q r) :
    productArrowRestrict n a.val q r (productArrow_source n b c a).symm
      (productArrow_target n b c a).symm (productUniversalArrow n b c) = a := by
  apply Subtype.ext
  exact Category.comp_id a.val

/-- The identity scheme map recovers the identity on any original-family test. -/
theorem productIdentityMap_apply (q : T ⟶ normalizedLocus n b) :
    q ≫ productIdentityMap n b = (productArrowId n q).val := by
  exact congrArg Subtype.val
    (productArrowRestrict_id n q q (Category.comp_id q).symm)

/-- The inverse scheme map recovers the inverse of every specified arrow. -/
theorem productInverseMap_apply (a : ProductArrow n q r) :
    a.val ≫ productInverseMap n b c = (productArrowInv n a).val := by
  have h := productArrowRestrict_inv n a.val q r (productArrow_source n b c a).symm
    (productArrow_target n b c a).symm (productUniversalArrow n b c)
  rw [productUniversalArrow_restrict] at h
  exact congrArg Subtype.val h

/-- The composition scheme map recovers the composite of every specified composable pair. -/
theorem productCompositionMap_apply (a : ProductArrow n q r) (z : ProductArrow n r s) :
    productComposableLift n b c d a z ≫ productCompositionMap n b c d =
      (productArrowComp n a z).val := by
  let l := productComposableLift n b c d a z
  have hq : q = l ≫ (productComposableFirst n b c d ≫ productArrowSource n b c) := by
    rw [← Category.assoc, productComposableLift_first, productArrow_source]
  have hr : r = l ≫ (productComposableFirst n b c d ≫ productArrowTarget n b c) := by
    rw [← Category.assoc, productComposableLift_first, productArrow_target]
  have hs : s = l ≫ (productComposableSecond n b c d ≫ productArrowTarget n c d) := by
    rw [← Category.assoc, productComposableLift_second, productArrow_target]
  have ha : productArrowRestrict n l q r hq hr (productComposableFirstArrow n b c d) = a :=
    Subtype.ext (productComposableLift_first n b c d a z)
  have hz : productArrowRestrict n l r s hr hs (productComposableSecondArrow n b c d) = z :=
    Subtype.ext (productComposableLift_second n b c d a z)
  have h := productArrowRestrict_comp n l q r hq hr s hs
    (productComposableFirstArrow n b c d) (productComposableSecondArrow n b c d)
  rw [ha, hz] at h
  exact congrArg Subtype.val h

end FLT.Mazur.CyclicCharacteristicAtlas
