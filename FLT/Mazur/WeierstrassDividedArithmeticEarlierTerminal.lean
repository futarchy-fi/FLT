/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNilpotentEarlierTerminal
public import FLT.Mazur.WeierstrassDividedArithmeticBoundaryCharts

/-!
# Full nonadjacent terminal intersections in the original arithmetic stages

Every indexed chart beyond the newest exterior has empty intersection with
the whole terminal divided chart at every original arithmetic quotient order.
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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
  (j : ℕ) (hj : j ≤ n) (i : Fin (j + 3)) (hi : 3 ≤ i.val)
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "E" => pullbackSymmetry q (finiteGlobalStructure hπ data j hj)
local notation "old" => globalTensorAtlasMap hπ data Q j hj i
local notation "terminal" => globalDividedTensorChart hπ data Q j hj

include hi in
/-- Every nonadjacent indexed chart misses the complete terminal arithmetic chart. -/
theorem earlierArithmeticTensor_terminal_disjoint :
    Disjoint (Set.range (old ≫ (E).hom)) (Set.range (terminal ≫ (E).hom)) := by
  have hp : IsNilpotent (algebraMap R Q π) := ⟨m + 1, parameter_pow R π m⟩
  have H := globalTensorAtlas_terminal_nonadjacent_nilpotent_disjoint
    hπ data Q j hj hp i hi
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have he : terminal y = old x := (E).hom.homeomorph.injective hy
  exact Set.disjoint_left.mp H ⟨x, rfl⟩ ⟨y, he⟩

include hi in
/-- The entire nonadjacent terminal fiber product is empty at every arithmetic order. -/
theorem earlierArithmeticTensor_terminal_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (old ≫ (E).hom) (terminal ≫ (E).hom) := by
  let _ := Scheme.isEmpty_pullback (old ≫ (E).hom) (terminal ≫ (E).hom)
    (earlierArithmeticTensor_terminal_disjoint hπ data m j hj i hi)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback (old ≫ (E).hom) (terminal ≫ (E).hom))))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

/-- The empty source identifies the full original terminal arithmetic intersection. -/
def earlierArithmeticTensorTerminalPullbackIso :
    (∅ : Scheme) ≅ pullback (old ≫ (E).hom) (terminal ≫ (E).hom) :=
  (earlierArithmeticTensor_terminal_isPullback hπ data m j hj i hi).isoPullback

end FLT.Mazur.WeierstrassDividedDepth
