/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalTerminalComponents
public import FLT.Mazur.WeierstrassDividedTerminalComponentStructure
public import FLT.Mazur.WeierstrassDividedFinalNodeCoproduct

/-!
# The actual terminal component pair over the residue field

These are the original projective-line maps with endpoints in the original
node family. Their two-summand coproduct is only part of the full normalization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (s + 1) hs)

/-- Both complete components retain the original residue-field structure. -/
@[reassoc] theorem finalTerminalComponent_structure (i : Fin 2) :
    finalTerminalComponent hπ data D s hs hk hp i ≫ p = ProjectiveLine.toBase K := by
  by_cases h : 0 < start + s
  · rw [finalTerminalComponent_positive hπ data D s hs hk hp h]
    fin_cases i
    · exact terminalFirstComponent_structure hπ data D s hs hk hp h
    · exact terminalSecondComponent_structure hπ data D s hs hk hp h
  · rw [finalTerminalComponent_zero_depth hπ data D s hs hk hp (by omega)]
    fin_cases i
    · exact terminalZeroFirstComponent_structure hπ data D s hs hk hp (by omega)
    · exact terminalZeroSecondComponent_structure hπ data D s hs hk hp (by omega)

/-- The actual full terminal component as a map over the residue field. -/
def finalTerminalOverComponent (i : Fin 2) : PolygonPinching.component K ⟶ Over.mk p :=
  Over.homMk (finalTerminalComponent hπ data D s hs hk hp i)
    (finalTerminalComponent_structure hπ data D s hs hk hp i)

/-- The zero endpoint is the original ordered retained node, over the field. -/
@[reassoc] theorem finalTerminalOverComponent_zero (i : Fin 2) :
    ProjectiveLine.zeroSection K ≫ finalTerminalOverComponent hπ data D s hs hk hp i =
      finalNodeOverSection hπ data D s hs hk hp (.inl (.inr (⟨s, by omega⟩, i))) := by
  apply Over.OverMorphism.ext
  exact finalTerminalComponent_zero hπ data D s hs hk hp i

/-- The common infinity endpoint is the original terminal node, over the field. -/
@[reassoc] theorem finalTerminalOverComponent_infinity (i : Fin 2) :
    ProjectiveLine.infinitySection K ≫ finalTerminalOverComponent hπ data D s hs hk hp i =
      finalNodeOverSection hπ data D s hs hk hp (.inr ()) := by
  apply Over.OverMorphism.ext
  exact finalTerminalComponent_infinity hπ data D s hs hk hp i

/-- The two component maps cannot coincide because their original zero nodes differ. -/
theorem finalTerminalComponent_injective :
    Function.Injective (finalTerminalComponent hπ data D s hs hk hp) := by
  intro a b he
  have H := congrArg (fun f => ProjectiveLine.zero K ≫ f) he
  rw [finalTerminalComponent_zero, finalTerminalComponent_zero] at H
  have hi := finalNodeSection_injective hπ data D s hs hk hp H
  exact (Prod.mk.inj (Sum.inr.inj (Sum.inl.inj hi))).2

/-- The two terminal components as an actual partial normalization coproduct. -/
def finalTerminalComponentCoproduct : PolygonPinching.components K 2 ⟶ Over.mk p :=
  Sigma.desc (finalTerminalOverComponent hπ data D s hs hk hp)

/-- Every summand of the partial normalization retains its original map. -/
@[reassoc] theorem finalTerminalComponentCoproduct_ι (i : Fin 2) :
    PolygonPinching.componentι K 2 i ≫ finalTerminalComponentCoproduct hπ data D s hs hk hp =
      finalTerminalOverComponent hπ data D s hs hk hp i :=
  Sigma.ι_comp_desc _ _

end FLT.Mazur.WeierstrassDividedDepth
