/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductOperationTests

/-!
# Groupoid equations for the ordered-pair scheme operations

The equations hold on every scheme test, and in particular on the universal
arrow schemes. All equalities compare actual morphisms of schemes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme} {b c d e : Bool}
  {q : T ⟶ normalizedLocus n b} {r : T ⟶ normalizedLocus n c}
  {s : T ⟶ normalizedLocus n d} {t : T ⟶ normalizedLocus n e}

/-- Inversion is involutive on actual parameters. -/
theorem productArrowInv_inv (a : ProductArrow n q r) :
    productArrowInv n (productArrowInv n a) = a := by
  apply productArrow_ext n
  rw [productArrowInv_eval, productArrowInv_eval]
  apply CompatibleIso.ext_curve
  rfl

/-- The two inversion scheme maps are inverse morphisms. -/
@[reassoc] theorem productInverseMap_involutive (b c : Bool) :
    productInverseMap n b c ≫ productInverseMap n c b = 𝟙 _ := by
  have h := productInverseMap_apply n (productArrowInv n (productUniversalArrow n b c))
  rw [productArrowInv_inv] at h
  exact h

/-- Inversion is an isomorphism of the two ordered-pair comparison schemes. -/
def productInverseIso (b c : Bool) : productSubgroupScheme n b c ≅ productSubgroupScheme n c b :=
  ⟨productInverseMap n b c, productInverseMap n c b,
    productInverseMap_involutive n b c, productInverseMap_involutive n c b⟩

/-- Left unit equation on any actual scheme test. -/
theorem productCompositionMap_left_unit (a : ProductArrow n q r) :
    productComposableLift n b b c (productArrowId n q) a ≫ productCompositionMap n b b c =
      a.val := by
  rw [productCompositionMap_apply, productArrowId_comp]

/-- Right unit equation on any actual scheme test. -/
theorem productCompositionMap_right_unit (a : ProductArrow n q r) :
    productComposableLift n b c c a (productArrowId n r) ≫ productCompositionMap n b c c =
      a.val := by
  rw [productCompositionMap_apply, productArrowComp_id]

/-- Right inverse equation on any actual scheme test. -/
theorem productCompositionMap_right_inverse (a : ProductArrow n q r) :
    productComposableLift n b c b a (productArrowInv n a) ≫ productCompositionMap n b c b =
      q ≫ productIdentityMap n b := by
  rw [productCompositionMap_apply, productArrowComp_inv, productIdentityMap_apply]

/-- Left inverse equation on any actual scheme test. -/
theorem productCompositionMap_left_inverse (a : ProductArrow n q r) :
    productComposableLift n c b c (productArrowInv n a) a ≫ productCompositionMap n c b c =
      r ≫ productIdentityMap n c := by
  rw [productCompositionMap_apply, productArrowInv_comp, productIdentityMap_apply]

/-- Associativity compares the actual two composite scheme maps on every test. -/
theorem productCompositionMap_associative (a : ProductArrow n q r) (z : ProductArrow n r s)
    (w : ProductArrow n s t) :
    productComposableLift n b d e (productArrowComp n a z) w ≫ productCompositionMap n b d e =
      productComposableLift n b c e a (productArrowComp n z w) ≫ productCompositionMap n b c e := by
  rw [productCompositionMap_apply, productCompositionMap_apply, productArrowComp_assoc]

/-- The universal left unit diagram is an equality of scheme morphisms. -/
theorem productCompositionMap_universal_left_unit (b c : Bool) :
    productComposableLift n b b c (productArrowId n (productArrowSource n b c))
        (productUniversalArrow n b c) ≫ productCompositionMap n b b c = 𝟙 _ :=
  productCompositionMap_left_unit n (productUniversalArrow n b c)

/-- The universal right unit diagram is an equality of scheme morphisms. -/
theorem productCompositionMap_universal_right_unit (b c : Bool) :
    productComposableLift n b c c (productUniversalArrow n b c)
        (productArrowId n (productArrowTarget n b c)) ≫ productCompositionMap n b c c = 𝟙 _ :=
  productCompositionMap_right_unit n (productUniversalArrow n b c)

end FLT.Mazur.CyclicCharacteristicAtlas
