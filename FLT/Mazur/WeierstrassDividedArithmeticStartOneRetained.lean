/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedStartOneQuotient
public import FLT.Mazur.WeierstrassDividedArithmeticFixedRetainedRestriction

/-!
# Unconditional retained compatibility at starting thickness one

The quotient, the full corrections, and every depth scale are constructed.
All retained labels map to the original normalized polygon, preserve its
quotient arrows, and recover the original first-retained comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n)

/-- The constructed comparison at every retained label for original starting thickness one. -/
def arithmeticStartOneRetainedMap (a : Fin k) (b : Bool) :
    arithmeticLabeledAtlasObject hπ data H m k hk (.retained a b) ⟶
      arithmeticFactorRatioPolygon π m W (π ^ 1) H.a1_unit H.scale_div k :=
  arithmeticFixedRetainedMap hπ data H m k hk (arithmeticStartOneQuotient W H.a1_unit π m)
    (arithmeticStartOneQuotient_relation W H.a1_unit π m) a b

omit [IsBezout R] in
/-- Every full consecutive edge agrees, with no assumed correction or unit quotient. -/
@[reassoc] theorem arithmeticStartOneRetainedMap_adjacent
    (a : ℕ) (ha : a + 1 < k) (b : Bool) :
    leftBranchOpen (Quotient R π m) (parameter R π m) ≫
        arithmeticStartOneRetainedMap hπ data H m k hk ⟨a, by omega⟩ b =
      precedingBranch (Quotient R π m) (parameter R π m) ≫
        arithmeticStartOneRetainedMap hπ data H m k hk ⟨a + 1, ha⟩ b :=
  arithmeticFixedRetainedMap_adjacent hπ data H m k hk _ _ a ha b

omit [IsBezout R] in
/-- The actual quotient square commutes at every retained depth and original label. -/
@[reassoc] theorem arithmeticStartOneRetainedMap_restriction (a : Fin k) (b : Bool) :
    arithmeticStartOneRetainedMap hπ data H m k hk a b ≫
      arithmeticFactorRatioPolygonRestriction π m W (π ^ 1) H.a1_unit H.scale_div k =
    arithmeticLabeledAtlasRestriction hπ data H m k hk (.retained a b) ≫
      arithmeticStartOneRetainedMap hπ data H (m + 1) k hk a b :=
  arithmeticFixedRetainedMap_restriction hπ data H m k hk _ _ _ _
    (arithmeticStartOneQuotient_restriction W H.a1_unit π m) a b

omit [IsBezout R] in
/-- The recursively scaled family starts with the original full first-retained comparison. -/
theorem arithmeticStartOneRetainedMap_first (hk0 : 0 < k) (b : Bool) :
    arithmeticStartOneRetainedMap hπ data H m k hk ⟨0, hk0⟩ b =
      arithmeticFactorRatioFirstRetainedMap hπ data H m k hk hk0 b :=
  arithmeticFixedRetainedMap_first hπ data H m k hk _ _ hk0
    (arithmeticStartOneQuotient_first W H.a1_unit π m hπ H.scale_div) b

end FLT.Mazur.WeierstrassDividedDepth
