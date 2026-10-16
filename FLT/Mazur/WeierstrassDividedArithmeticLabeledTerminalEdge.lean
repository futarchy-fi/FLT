/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticNewestIndex
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledAtlas
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalPunctureIntersection

/-!
# Full standard terminal edges in the labeled arithmetic atlas

The last retained label meets the entire normalized terminal node along its
standard puncture. The other projection retains the original Laurent comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (j : ℕ) (hj : j + 1 ≤ n)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "s" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W
  (π ^ (start + (j + 1))) (Data.b3 d) (Data.b4 d) (Data.b6 d)
    H.a1_unit (H.scale (j + 1)) H.a2_div (H.b4_div _) (H.b6_div _)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
variable (b : Bool)
local notation "δ" => ite (b = true) (NodalFiber.p s) (NodalFiber.q s)
local notation "i" => Spec.map (CommRingCat.ofHom
  (algebraMap (NodalFiber.Coordinate s) (Localization.Away δ)))
local notation "P" => terminalArithmeticPunctureIso data m j hj H.a1_unit
  (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) b

/-- The terminal/last-label fiber product is precisely the complete standard node puncture. -/
theorem arithmeticLabeledAtlas_terminal_edge_isPullback :
    IsPullback i ((P).inv ≫ PolygonSmoothing.leftBranchOpen Q (parameter R π m))
      (c .terminal) (c (.retained ⟨j, by omega⟩ b)) := by
  dsimp only [arithmeticLabeledAtlasMap, arithmeticLabeledTerminalChart,
    arithmeticLabeledRetainedChart]
  rw [arithmeticRetainedTensorChart_newest]
  exact terminalArithmeticStandardPuncture_isPullback data m j hj H.a1_unit
    (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) b hπ

attribute [local irreducible] terminalArithmeticPunctureIso arithmeticLabeledAtlasMap

/-- The full standard terminal edge commutes with the exact labeled atlas maps. -/
@[reassoc] theorem arithmeticLabeledAtlas_terminal_edge_overlap :
    i ≫ c .terminal =
      (P).inv ≫ PolygonSmoothing.leftBranchOpen Q (parameter R π m) ≫
        c (.retained ⟨j, by omega⟩ b) := by
  simpa only [Category.assoc] using
    (arithmeticLabeledAtlas_terminal_edge_isPullback hπ data H m j hj b).w

/-- The actual labeled terminal intersection is isomorphic to the standard puncture scheme. -/
def arithmeticLabeledTerminalEdgePullbackIso :
    Spec (.of (Localization.Away δ)) ≅
      pullback (c .terminal) (c (.retained ⟨j, by omega⟩ b)) :=
  (arithmeticLabeledAtlas_terminal_edge_isPullback hπ data H m j hj b).isoPullback

/-- The fiber-product comparison preserves the full terminal puncture inclusion. -/
@[reassoc] theorem arithmeticLabeledTerminalEdgePullbackIso_terminal :
    (arithmeticLabeledTerminalEdgePullbackIso hπ data H m j hj b).hom ≫
      pullback.fst _ _ = i :=
  (arithmeticLabeledAtlas_terminal_edge_isPullback hπ data H m j hj b).isoPullback_hom_fst

/-- The fiber-product comparison preserves the original last-branch Laurent morphism. -/
@[reassoc] theorem arithmeticLabeledTerminalEdgePullbackIso_retained :
    (arithmeticLabeledTerminalEdgePullbackIso hπ data H m j hj b).hom ≫
      pullback.snd _ _ = (P).inv ≫ PolygonSmoothing.leftBranchOpen Q (parameter R π m) :=
  (arithmeticLabeledAtlas_terminal_edge_isPullback hπ data H m j hj b).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
