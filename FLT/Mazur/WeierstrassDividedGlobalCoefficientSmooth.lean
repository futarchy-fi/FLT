/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalCoefficientCartesian

/-!
# Smooth surjective whole actions over arbitrary coefficient algebras

The actual coefficient action square transfers the geometry of the original
whole action. This includes nonflat coefficient extensions and singular fibers.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n) (S : Type u) [CommRing S] [Algebra R S]

/-- Every whole coefficient-extended action is smooth. -/
instance finiteGlobalCoefficientAction_smooth :
    Smooth (finiteGlobalCoefficientAction hπ data j hj S) :=
  MorphismProperty.of_isPullback (finiteGlobalCoefficientAction_isPullback hπ data j hj S)
    (inferInstance : Smooth (finiteGlobalAction hπ data j hj))

/-- The actual action remains flat under arbitrary coefficient extension. -/
theorem finiteGlobalCoefficientAction_flat :
    Flat (finiteGlobalCoefficientAction hπ data j hj S) := inferInstance

/-- Every point of the entire tensor model lies in the extended action image. -/
instance finiteGlobalCoefficientAction_surjective :
    Surjective (finiteGlobalCoefficientAction hπ data j hj S) :=
  MorphismProperty.of_isPullback (finiteGlobalCoefficientAction_isPullback hπ data j hj S)
    (inferInstance : Surjective (finiteGlobalAction hπ data j hj))

end FLT.Mazur.WeierstrassDividedDepth
