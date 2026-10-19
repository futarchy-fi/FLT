/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductClassifierRestriction

/-!
# Groupoid operations on ordered-pair parameters

The operations classify actual identity, inverse, and composite compatible
isomorphisms. The groupoid laws retain all arrows, including stabilizers.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
variable (n : ℕ) [NeZero n] {T : Scheme}
  {b c d e : Bool} {q : T ⟶ normalizedLocus n b}
  {r : T ⟶ normalizedLocus n c} {s : T ⟶ normalizedLocus n d}
  {t : T ⟶ normalizedLocus n e}

/-- Parameters with specified ordered endpoints on a scheme test. -/
abbrev ProductArrow (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c) :=
  {k : T ⟶ productSubgroupScheme n b c //
    k ≫ productSubgroupStructure n b c = prod.lift q r}

/-- Identity parameter on the specified original family. -/
def productArrowId (q : T ⟶ normalizedLocus n b) : ProductArrow n q q :=
  productCompatibleParameter n b b q q
    (CompatibleIso.refl ((normalizedSubgroup n b).baseChange q))

/-- Inverse parameter retains the inverse compatible isomorphism. -/
def productArrowInv (a : ProductArrow n q r) : ProductArrow n r q :=
  productCompatibleParameter n c b r q
    (productCompatibleTestComparison n b c q r a).symm

/-- Composite parameter retains the composite compatible isomorphism. -/
def productArrowComp (a : ProductArrow n q r) (z : ProductArrow n r s) :
    ProductArrow n q s :=
  productCompatibleParameter n b d q s
    ((productCompatibleTestComparison n b c q r a).trans
      (productCompatibleTestComparison n c d r s z))

/-- Evaluation of the identity parameter. -/
@[simp] theorem productArrowId_eval (q : T ⟶ normalizedLocus n b) :
    productCompatibleTestComparison n b b q q (productArrowId n q) =
      CompatibleIso.refl ((normalizedSubgroup n b).baseChange q) :=
  productCompatibleParameter_recovers n b b q q _

/-- Evaluation of the inverse parameter. -/
@[simp] theorem productArrowInv_eval (a : ProductArrow n q r) :
    productCompatibleTestComparison n c b r q (productArrowInv n a) =
      (productCompatibleTestComparison n b c q r a).symm :=
  productCompatibleParameter_recovers n c b r q _

/-- Evaluation of the composite parameter. -/
@[simp] theorem productArrowComp_eval (a : ProductArrow n q r) (z : ProductArrow n r s) :
    productCompatibleTestComparison n b d q s (productArrowComp n a z) =
      (productCompatibleTestComparison n b c q r a).trans
        (productCompatibleTestComparison n c d r s z) :=
  productCompatibleParameter_recovers n b d q s _

/-- Evaluation detects equality of actual parameters. -/
theorem productArrow_ext {a z : ProductArrow n q r}
    (h : productCompatibleTestComparison n b c q r a =
      productCompatibleTestComparison n b c q r z) : a = z :=
  (productCompatibleSchemePointEquiv n b c q r).injective h

/-- Left unit for actual parameters. -/
theorem productArrowId_comp (a : ProductArrow n q r) :
    productArrowComp n (productArrowId n q) a = a := by
  apply productArrow_ext n
  simp only [productArrowComp_eval, productArrowId_eval, CompatibleIso.refl_trans]

/-- Right unit for actual parameters. -/
theorem productArrowComp_id (a : ProductArrow n q r) :
    productArrowComp n a (productArrowId n r) = a := by
  apply productArrow_ext n
  simp only [productArrowComp_eval, productArrowId_eval, CompatibleIso.trans_refl]

/-- Associativity for actual parameters. -/
theorem productArrowComp_assoc (a : ProductArrow n q r) (z : ProductArrow n r s)
    (w : ProductArrow n s t) :
    productArrowComp n (productArrowComp n a z) w =
      productArrowComp n a (productArrowComp n z w) := by
  apply productArrow_ext n
  simp only [productArrowComp_eval, CompatibleIso.trans_assoc]

/-- The inverse parameter is a right inverse. -/
theorem productArrowComp_inv (a : ProductArrow n q r) :
    productArrowComp n a (productArrowInv n a) = productArrowId n q := by
  apply productArrow_ext n
  simp only [productArrowComp_eval, productArrowInv_eval, productArrowId_eval,
    CompatibleIso.trans_symm]

/-- The inverse parameter is a left inverse. -/
theorem productArrowInv_comp (a : ProductArrow n q r) :
    productArrowComp n (productArrowInv n a) a = productArrowId n r := by
  apply productArrow_ext n
  simp only [productArrowComp_eval, productArrowInv_eval, productArrowId_eval,
    CompatibleIso.symm_trans]

end FLT.Mazur.CyclicCharacteristicAtlas
