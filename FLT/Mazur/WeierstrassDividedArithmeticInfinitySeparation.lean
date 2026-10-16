/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNilpotentInfinity
public import FLT.Mazur.WeierstrassDividedArithmeticBoundaryCharts

/-!
# Full positive-depth arithmetic charts have empty infinity intersections

The actual terminal and retained arithmetic charts miss the original infinity
chart at every quotient order. The full schemes, not just sections, are separated.
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

local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
variable (j : ℕ) (hj : j ≤ n) (hk : 0 < start + j)
local notation "E" => pullbackSymmetry q (finiteGlobalStructure hπ data j hj)
local notation "t" => globalDividedTensorChart hπ data Q j hj ≫ Iso.hom E
local notation "i" => finiteInfinityTensorChart hπ data Q j hj ≫ Iso.hom E

include hk in
/-- The entire positive-depth terminal arithmetic chart misses the original infinity chart. -/
theorem terminalArithmetic_infinity_disjoint : Disjoint (Set.range t) (Set.range i) := by
  have hp : IsNilpotent (algebraMap R Q π) := ⟨m + 1, parameter_pow R π m⟩
  have H := globalDividedTensor_nilpotent_infinity_disjoint Q hπ data hp j hj hk
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  exact Set.disjoint_left.mp H ⟨x, rfl⟩ ⟨y, (E).hom.homeomorph.injective hy⟩

include hk in
/-- The full terminal/infinity fiber product is the empty scheme at every arithmetic order. -/
theorem terminalArithmetic_infinity_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) t i := by
  let _ := Scheme.isEmpty_pullback t i
    (terminalArithmetic_infinity_disjoint hπ data m j hj hk)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback t i)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

variable (hnext : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "E₁" => pullbackSymmetry q (finiteGlobalStructure hπ data (j + 1 + r) hr)
local notation "c" => finiteArithmeticOlderTensorChart hπ data m j hnext r hr
local notation "i₁" => finiteInfinityTensorChart hπ data Q (j + 1 + r) hr ≫ Iso.hom E₁

include hk in
/-- Every full retained positive-depth arithmetic chart is disjoint from the infinity chart. -/
theorem olderArithmetic_infinity_disjoint : Disjoint (Set.range c) (Set.range i₁) := by
  have hp : IsNilpotent (algebraMap R Q π) := ⟨m + 1, parameter_pow R π m⟩
  have H := olderGlobalNilpotent_infinity_disjoint Q hπ data j hnext r hr hp hk
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  exact Set.disjoint_left.mp H ⟨x, rfl⟩ ⟨y, (E₁).hom.homeomorph.injective hy⟩

include hk in
/-- The full retained-chart/infinity fiber product remains empty throughout the arithmetic tower. -/
theorem olderArithmetic_infinity_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) c i₁ := by
  let _ := Scheme.isEmpty_pullback c i₁
    (olderArithmetic_infinity_disjoint hπ data m j hk hnext r hr)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback c i₁)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end FLT.Mazur.WeierstrassDividedDepth
