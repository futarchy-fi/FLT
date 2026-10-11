/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoExteriorRestriction
public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoTerminalRestriction
public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoHomExt
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoGlobalDesc

import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoExteriorRestriction

import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoTerminalRestriction

/-!
# Global descent restricts to every complete cyclic component

The actual component maps satisfy existence and uniqueness of descent for
every compatible family of morphisms to an arbitrary scheme.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hs : 0 + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + 0 + 1) ≤ depth)
  (hp : 2 * (start + 0 + 1) = depth)
variable {Y : Scheme.{u}}
  (F : Fin 2 → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => zeroEqualityLengthTwoGlobalDesc hπ data D hs hstart hk hp F w

local notation "Z" => zeroEqualityCycleComponent hπ data D 0 hs hstart hk hp

/-- Every complete original cyclic component recovers its prescribed family map. -/
@[reassoc] theorem zeroEqualityLengthTwoGlobalDesc_component (i : Fin 2) :
    (Z i).left ≫ d = F i := by
  fin_cases i
  · exact zeroEqualityLengthTwoGlobalDesc_exterior_component hπ data D hs hstart hk hp F w
  · exact zeroEqualityLengthTwoGlobalDesc_terminal_component hπ data D hs hstart hk hp F w

/-- The actual full component restrictions uniquely characterize the global descent. -/
theorem zeroEqualityLengthTwoGlobalDesc_component_unique
    (f : finiteGlobalTensorModel hπ data K (0 + 1) hs ⟶ Y)
    (hf : ∀ i, (Z i).left ≫ f = F i) : f = d := by
  apply zeroEqualityCycleComponent_hom_ext_lengthTwo hπ data D hs hstart hk hp
  intro i
  exact (hf i).trans (zeroEqualityLengthTwoGlobalDesc_component
      hπ data D hs hstart hk hp F w i).symm

include w in
/-- Every compatible projective family descends uniquely to the actual full residue model. -/
theorem zeroEqualityLengthTwo_existsUnique_desc :
    ∃! f : finiteGlobalTensorModel hπ data K (0 + 1) hs ⟶ Y,
      ∀ i, (Z i).left ≫ f = F i :=
  ⟨d, zeroEqualityLengthTwoGlobalDesc_component hπ data D hs hstart hk hp F w,
    fun f hf => zeroEqualityLengthTwoGlobalDesc_component_unique
      hπ data D hs hstart hk hp F w f hf⟩

end FLT.Mazur.WeierstrassDividedDepth
