/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthOuterInitial
public import FLT.Mazur.WeierstrassDividedThirdInitialAtlasRestriction

/-!
# The original initial source at depth two

The initial chart at depth two has not received a third correction. Its
comparison recovers the original full inclusion without expanding the atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThirdInitialAtlasChart arithmeticThirdAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (ha : 2 = j)
local notation "Q" => Quotient R π m
local notation "κ" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu
local notation "ι" => arithmeticThirdAtlasChart hπ data H m j hj u hu

/-- The depth-two initial source is the original polynomial node open. -/
def arithmeticThirdShallowInitialIdentification (b : Bool) :
    Spec (.of (PolynomialNodeOpen (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1)))) ≅
      arithmeticThirdInitialAtlasObject hπ data H m j hj u hu (.initial b) :=
  eqToIso (by simp only [arithmeticThirdInitialAtlasObject, show ¬j = 1 by omega,
    ↓reduceIte]; rfl)

/-- Its full inclusion is exactly the unchanged third-atlas inclusion. -/
@[reassoc] theorem arithmeticThirdShallowInitial_chart (b : Bool) :
    (arithmeticThirdShallowInitialIdentification hπ data H m j hj u hu ha b).hom ≫
      κ (.initial b) = ι (.initial b) := by
  have h := arithmeticThirdInitialAtlasCorrection_chart hπ data H m j hj u hu (.initial b)
  simpa only [arithmeticThirdInitialAtlasCorrection, show ¬j = 1 by omega, ↓reduceDIte,
    arithmeticThirdShallowInitialIdentification] using h

omit [IsBezout R] in
/-- The unchanged shallow source retains the full original initial coefficient quotient. -/
@[reassoc] theorem arithmeticThirdShallowInitialIdentification_restriction (b : Bool) :
    (arithmeticThirdShallowInitialIdentification hπ data H m j hj u hu ha b).hom ≫
      arithmeticThirdInitialAtlasRestriction hπ data H j hj u hu m (.initial b) =
        arithmeticFullInitialNodeQuotient R π m W (π ^ 1) ≫
          (arithmeticThirdShallowInitialIdentification hπ data H (m + 1) j hj u hu ha b).hom := by
  have h := arithmeticThirdInitialAtlasCorrection_restriction
    hπ data H j hj u hu m (.initial b)
  simpa only [arithmeticThirdInitialAtlasCorrection, show ¬j = 1 by omega, ↓reduceDIte,
    arithmeticThirdShallowInitialIdentification, arithmeticThirdAtlasRestriction_initial] using h

end FLT.Mazur.WeierstrassDividedDepth
