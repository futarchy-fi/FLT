/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfTriple
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalAnyDepthCoverage

/-!
# The last nonpunctured retained input reaches terminal addition

Move the first input along the actual terminal incidence boundary. The full
terminal self-pair has an intermediate or reciprocal output at triple depth.
Both original arithmetic inputs are preserved by the combined construction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "old" => finiteArithmeticNewestTensorChart hπ data m j hj
local notation "next" => finiteArithmeticDividedTensorChart hπ data m (j + 1) hj
local notation "E" => finiteDividedTensorAtlasIso hπ data Q (j + 1) hj
local notation "f" => old ≫ s
local notation "f'" => next ≫ s
local notation "g" => chart 1 ≫ s
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q (j + 1) hj 1
local notation "fg" => (O).ι ≫ chart 1 ≫ s
local notation "u" => tensorCoord W (π ^ (0 + j)) π (e).b3 (e).b4 (e).b6 Q 2
variable (hdepth : depth = 3 * (j + 1))
local notation "D" => arithmeticTerminalSelfTripleOpen node data m (j + 1) hj hdepth
local notation "F" => arithmeticTerminalSelfReciprocalOpen hπ data m (j + 1) hj

local instance arithmeticLastRetainedTriple_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- The last nonpunctured retained/terminal pair reaches a genuine output domain. -/
theorem arithmeticLastRetained_nonpunctured_triple_target
    (hgen : IsLocalRing.maximalIdeal R = ideal R π)
    (p : (pullback f g : Scheme))
    (hs : old (pullback.fst f g p) ∈ (s).smoothLocus)
    (ht : chart 1 (pullback.snd f g p) ∈ (s).smoothLocus)
    (hx : u ∈ (pullback.fst f g p).asIdeal) :
    ∃ z : (pullback fg fg : Scheme),
      chart 1 ((O).ι (pullback.fst fg fg z)) = old (pullback.fst f g p) ∧
      (O).ι (pullback.snd fg fg z) = pullback.snd f g p ∧ (z ∈ D ∨ z ∈ F) := by
  obtain ⟨q, hq, he, _⟩ := arithmeticTerminalPair_anyDepth_zero_coordinates
    hπ data node hgen m j hj g (by omega) p hs hx
  let transfer : pullback f' g ⟶ pullback g g :=
    pullback.lift (pullback.fst f' g ≫ (E).hom) (pullback.snd f' g) (by
      simp only [Category.assoc, arithmeticTensorAtlas_terminal_assoc]
      exact pullback.condition)
  have hf : transfer ≫ pullback.fst g g ≫ chart 1 = pullback.fst f' g ≫ next := by
    simp only [transfer, pullback.lift_fst_assoc, Category.assoc,
      arithmeticTensorAtlas_terminal]
  have hg : transfer ≫ pullback.snd g g = pullback.snd f' g := by
    simp only [transfer, pullback.lift_snd]
  have hfirst : chart 1 (pullback.fst g g (transfer q)) = old (pullback.fst f g p) :=
    (congrArg (fun morphism => morphism q) hf).trans hq
  have hsecond : pullback.snd g g (transfer q) = pullback.snd f g p :=
    (congrArg (fun morphism => morphism q) hg).trans he
  obtain ⟨z, hz, ht', hd⟩ := arithmeticTerminalSelfTriple_target
    node data m (j + 1) hj (by omega) hdepth (transfer q)
    (by rw [hfirst]; exact hs) (by rw [hsecond]; exact ht)
  exact ⟨z, (congrArg (chart 1) hz).trans hfirst, ht'.trans hsecond, hd⟩

end FLT.Mazur.WeierstrassDividedDepth
