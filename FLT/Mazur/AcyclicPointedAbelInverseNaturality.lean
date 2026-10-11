/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicPointedAbelBaseChange

/-!
# Naturality of the inverse acyclic pointed Abel correspondence

An intrinsic normalized class on a proper flat geometrically integral
Noetherian family constructs a unique full divisor on every pointed test.
The test base is unrestricted. When it too is locally Noetherian, this is
exactly the inverse of its intrinsic Abel equivalence.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {P X T S : Scheme.{0}} [IsLocallyNoetherian S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] [GeometricallyIntegral f] (h : IsPullback p q f g)
  (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  (d : T ⟶ P) (hd : d ≫ q = 𝟙 T) (hp : d ≫ p = g ≫ e)

/-- Construct the full divisor of a pulled-back intrinsic class on an arbitrary test base. -/
def acyclicPointedInverseTest (c : AcyclicRankOnePointedClass f e) :
    AcyclicRankOneRelativeDivisor q :=
  acyclicRelativeDivisorPullback h ((acyclicPointedAbelEquiv f e he).symm c)

/-- The constructed inverse on the test has precisely the pulled-back normalized class. -/
theorem acyclicPointedInverseTest_class (c : AcyclicRankOnePointedClass f e) :
    acyclicPointedAbel q d hd (acyclicPointedInverseTest h e he c) =
      acyclicPointedClassPullback h e d hp c := by
  unfold acyclicPointedInverseTest
  rw [acyclicPointedAbel_natural h e d hp he hd]
  exact congrArg (acyclicPointedClassPullback h e d hp)
    ((acyclicPointedAbelEquiv f e he).apply_symm_apply c)

/-- Uniqueness on arbitrary tests identifies full divisors, rather than their supports. -/
theorem acyclicPointedInverseTest_unique (c : AcyclicRankOnePointedClass f e)
    (D : AcyclicRankOneRelativeDivisor q)
    (hc : acyclicPointedAbel q d hd D = acyclicPointedClassPullback h e d hp c) :
    D = acyclicPointedInverseTest h e he c := by
  let _ : Surjective q := MorphismProperty.of_isPullback h inferInstance
  apply acyclicPointedAbel_injective q d hd
  exact hc.trans (acyclicPointedInverseTest_class h e he d hd hp c).symm

include he in
/-- Every pulled-back intrinsic class has a unique actual full relative divisor on the test. -/
theorem acyclicPointedInverseTest_existsUnique (c : AcyclicRankOnePointedClass f e) :
    ∃! D : AcyclicRankOneRelativeDivisor q,
      acyclicPointedAbel q d hd D = acyclicPointedClassPullback h e d hp c :=
  ⟨acyclicPointedInverseTest h e he c, acyclicPointedInverseTest_class h e he d hd hp c,
    fun D hc ↦ acyclicPointedInverseTest_unique h e he d hd hp c D hc⟩

include hd in
/-- Equal pulled-back classes from different original lines give equal full test ideals. -/
theorem acyclicPointedInverseTest_eq_of_class_eq (a b : AcyclicRankOnePointedClass f e)
    (hab : acyclicPointedClassPullback h e d hp a = acyclicPointedClassPullback h e d hp b) :
    acyclicPointedInverseTest h e he a = acyclicPointedInverseTest h e he b :=
  acyclicPointedInverseTest_unique h e he d hd hp b _
    ((acyclicPointedInverseTest_class h e he d hd hp a).trans hab)

/-- Over a locally Noetherian test, both intrinsic equivalences have the same full inverse. -/
theorem acyclicPointedAbelEquiv_symm_natural [IsLocallyNoetherian T]
    [IsProper q] [Flat q] [GeometricallyIntegral q]
    (c : AcyclicRankOnePointedClass f e) :
    (acyclicPointedAbelEquiv q d hd).symm (acyclicPointedClassPullback h e d hp c) =
      acyclicRelativeDivisorPullback h ((acyclicPointedAbelEquiv f e he).symm c) :=
  acyclicPointedInverseTest_unique h e he d hd hp c _
    ((acyclicPointedAbelEquiv q d hd).apply_symm_apply _)

end FLT.Mazur.CartierAbel
