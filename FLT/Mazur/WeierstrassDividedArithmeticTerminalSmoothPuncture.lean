/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalTensorProjection
public import FLT.Mazur.WeierstrassDividedNodalSmoothHorizontal
public import FLT.Mazur.WeierstrassDividedFiniteSecantInput
public import FLT.Mazur.SchemeArithmeticCoefficientSupport

/-!
# Smooth arithmetic terminal inputs below the middle are punctured

The full arithmetic smooth domain supplies the terminal horizontal puncture.
The proof tests its original integral coordinate prime and uses the quotient
only to establish closed-fiber support.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m j : ℕ) (hj : j ≤ n)
local notation "e" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "Q" => PolygonArithmeticStages.Quotient R π m
local notation "b" => (1 : Fin (j + 3))
local notation "A" => Coordinate W (π ^ (start + j)) (e).b3 (e).b4 (e).b6
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "coords" => tensorIntegralAtlasProjection hπ data Q j hj b
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj b
local notation "E" => finiteDividedTensorAtlasIso hπ data Q j hj
local notation "x₀" => x W (π ^ (start + j)) (e).b3 (e).b4 (e).b6

omit [IsNoetherianRing R] in
/-- Every original terminal arithmetic prime is supported on the closed fiber. -/
theorem arithmeticTerminalProjection_parameter_mem
    (p : globalTensorAtlasObject hπ data Q j hj b) :
    algebraMap R A π ∈ (coords p).asIdeal := by
  apply spectrumInput_parameter_mem π m coords
    (globalTensorAtlasMap hπ data Q j hj b ≫ pullback.fst q base) _ p
  rw [← finiteSecantDividedChart_structure hπ data j hj]
  exact tensorIntegralAtlasProjection_structure hπ data Q j hj b

/-- The full smooth arithmetic domain has relatively smooth integral terminal coordinates. -/
theorem arithmeticTerminalProjection_smooth
    (p : globalTensorAtlasObject hπ data Q j hj b) (hp : p ∈ O) :
    coords p ∈ (Spec.map (CommRingCat.ofHom (algebraMap R A))).smoothLocus := by
  have hs : finiteSecantDividedChart hπ data j hj (coords p) ∈ (base).smoothLocus := hp
  have he := Scheme.Hom.preimage_smoothLocus_eq
    (finiteSecantDividedChart hπ data j hj) base
  simp only [finiteSecantDividedChart_structure] at he
  exact he.le hs

/-- No terminal puncture premise is needed below middle depth on the full smooth domain. -/
theorem arithmeticTerminalProjection_nodal_punctured [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hj0 : 0 < start + j) (hm : 2 * (start + j) < depth)
    (p : globalTensorAtlasObject hπ data Q j hj b) (hp : p ∈ O) :
    x₀ ∉ (coords p).asIdeal :=
  nodalDivided_smooth_horizontal node e hj0 hm (coords p)
    (arithmeticTerminalProjection_parameter_mem hπ data m j hj p)
    (arithmeticTerminalProjection_smooth hπ data m j hj p hp)

/-- The puncture is in the original terminal tensor algebra at every arithmetic order. -/
theorem arithmeticTerminalTensor_nodal_punctured [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hj0 : 0 < start + j) (hm : 2 * (start + j) < depth)
    (p : globalTensorAtlasObject hπ data Q j hj b) (hp : p ∈ O) :
    tensorX W (π ^ (start + j)) (e).b3 (e).b4 (e).b6 Q ∉ ((E).inv p).asIdeal := by
  rw [← terminalTensorAtlasProjection_x_iff]
  exact arithmeticTerminalProjection_nodal_punctured hπ data m j hj node hj0 hm p hp

end FLT.Mazur.WeierstrassDividedDepth
