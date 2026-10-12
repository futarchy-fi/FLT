/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalHorizontalCyclicPair

/-!
# Actual terminal action on the independent universal Laurent pair

The coefficient action and universal projective scaling agree on the original
smooth-times-terminal source, retaining the original component label.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "𝕂" => ResidueField R
local notation "d" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D
local notation "q" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (ProjectiveLineUniversalAction.laurentPairEvaluation (K := 𝕂) τ⁻¹ z)))
local notation "C" => SmoothHorizontalResidueRing D
local notation "c" => Spec.map (CommRingCat.ofHom (algebraMap 𝕂 C))
local notation "V" => W.map (algebraMap R 𝕂)
local notation "v" => positiveEqualityCyclicSmoothGroupIso D s hk
local notation "o₁" => ProjectiveLineProductOverlap.left 𝕂[T;T⁻¹] ≫
  ProjectiveLineProductCharts.productChartMap 𝕂 𝕂[T;T⁻¹] true

local notation "B" => finiteGlobalCoefficientOverAction hπ data (s + 1) hs 𝕂

/-- The actual terminal action is universal scaling on the independent pair. -/
theorem terminalHorizontalCyclicAction_pair :
    q ≫ o₁ ≫ (((v).hom.hom.hom.hom ⊗ₘ Z ⟨s + 2, by omega⟩) ≫ B).left =
      q ≫ o₁ ≫
        (ProjectiveLineUniversalAction.act 𝕂 ≫ Z ⟨s + 2, by omega⟩).left := by
  have h := congrArg (· ≫ (B).left)
    (terminalHorizontalCyclicInput_pair hπ data D s hs hstart hk hp)
  have h₂ := congrArg Over.Hom.left
    (terminalHorizontalTensorOutput_over hπ data D s hs hstart hk hp)
  have h₃ := terminalIntegralTensorOutput_universal hπ data D s hs hstart hk hp
  simpa only [Over.comp_left, Category.assoc, ProjectiveLineUniversalAction.act,
    Over.homMk_left, terminalHorizontalTensorOverPoint] using h.trans (h₂.trans h₃)

end FLT.Mazur.WeierstrassDividedDepth
