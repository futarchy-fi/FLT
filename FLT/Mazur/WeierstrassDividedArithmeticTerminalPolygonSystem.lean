/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationCoherentTerminalPolygon
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledSystem
public import FLT.Mazur.PolygonArithmeticSystem

/-!
# The original terminal label maps naturally to polygon label zero

A primitive terminal divided constant coefficient supplies the compatible
normalization. The source is the actual labeled chart system, with every
original quotient arrow, including arrows skipping several orders.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (k : ℕ) (hk : k ≤ n)
local notation "d" => data (Fin.mk k (Nat.lt_succ_of_le hk))
variable (u : Rˣ) (hprimitive : Data.b6 (data ⟨k, Nat.lt_succ_of_le hk⟩) = π * ↑u)
include hprimitive

/-- A specific map of the original terminal chart to label zero of the intended polygon. -/
def arithmeticTerminalCoherentPolygonMap (m : ℕ) :
    arithmeticLabeledAtlasObject hπ data H m k hk .terminal ⟶
      (family R π m (2 * k + 3) (by omega)).left :=
  coherentTerminalPolygonMap π W (π ^ (start + k))
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale k) H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _) u hprimitive m (2 * k + 3) (by omega) ⟨0, by omega⟩

instance arithmeticTerminalCoherentPolygonMap_isOpenImmersion (m : ℕ) :
    IsOpenImmersion (arithmeticTerminalCoherentPolygonMap hπ data H k hk u hprimitive m) := by
  unfold arithmeticTerminalCoherentPolygonMap
  infer_instance

omit [IsBezout R] in
/-- Every original adjacent terminal quotient arrow commutes with the comparison. -/
@[reassoc] theorem arithmeticTerminalCoherentPolygonMap_restriction (m : ℕ) :
    arithmeticLabeledAtlasRestriction hπ data H m k hk .terminal ≫
      arithmeticTerminalCoherentPolygonMap hπ data H k hk u hprimitive (m + 1) =
    arithmeticTerminalCoherentPolygonMap hπ data H k hk u hprimitive m ≫
      stageRestriction R π m (2 * k + 3) (by omega) :=
  coherentTerminalPolygonMap_restriction π W (π ^ (start + k))
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale k) H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _) u hprimitive hπ m (2 * k + 3) (by omega) ⟨0, by omega⟩

/-- The original full terminal system has a specific natural polygon comparison. -/
def arithmeticTerminalPolygonSystem :
    arithmeticLabeledChartSystem hπ data H k hk .terminal ⟶
      stageSystem R π (2 * k + 3) (by omega) :=
  NatTrans.ofSequence (arithmeticTerminalCoherentPolygonMap hπ data H k hk u hprimitive) (by
    intro m
    simpa only [arithmeticLabeledChartSystem, stageSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
        arithmeticTerminalCoherentPolygonMap_restriction hπ data H k hk u hprimitive m)

omit [IsBezout R] in
/-- The terminal comparison also preserves every nonadjacent original quotient arrow. -/
@[reassoc] theorem arithmeticTerminalPolygonSystem_naturality {a b : ℕ} (hab : a ≤ b) :
    (arithmeticLabeledChartSystem hπ data H k hk .terminal).map (homOfLE hab) ≫
      arithmeticTerminalCoherentPolygonMap hπ data H k hk u hprimitive b =
    arithmeticTerminalCoherentPolygonMap hπ data H k hk u hprimitive a ≫
      (stageSystem R π (2 * k + 3) (by omega)).map (homOfLE hab) :=
  (arithmeticTerminalPolygonSystem hπ data H k hk u hprimitive).naturality (homOfLE hab)

end FLT.Mazur.WeierstrassDividedDepth
