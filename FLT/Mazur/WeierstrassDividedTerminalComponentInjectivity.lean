/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineMapInjectivity
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import FLT.Mazur.WeierstrassDividedTerminalComponents
public import FLT.Mazur.WeierstrassDividedTerminalZeroComponents

/-!
# Pointwise injectivity of the complete terminal components

The full parameter and its opposite terminal branch have exactly the original
Laurent intersection, including the stage-zero case.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
  (hp : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) hp (Data.b6 d) (Data.factor6 d))
local notation "E" => conicZeroAffineIso c hc

/-- The complete first terminal component is injective on all scheme points. -/
theorem terminalFirstComponent_point_injective (hk0 : 0 < start + j) :
    Function.Injective (terminalFirstComponent hπ data D j hj hk0 hk hp) := by
  apply ProjectiveLine.map_injective_of_parameter_pullback
    (terminalFirstComponent hπ data D j hj hk0 hk hp) (E) (𝟙 _)
    (terminalConicFirstParameter hπ data D j hj hk0 hk)
    (terminalConicSecondBranch hπ data D j hj hk hp)
  · exact Function.injective_id
  · unfold terminalConicFirstParameter
    exact Scheme.Hom.injective _
  · unfold terminalConicSecondBranch
    exact Scheme.Hom.injective _
  · exact terminalFirstComponent_left hπ data D j hj hk0 hk hp
  · simpa only [Category.id_comp] using
      terminalFirstComponent_right hπ data D j hj hk0 hk hp
  · rw [Category.comp_id, conicZeroAffineIso_puncture]
    exact terminalConicFirstParameter_isPullback hπ data D j hj hk0 hk hp

/-- The complete second terminal component is injective on all scheme points. -/
theorem terminalSecondComponent_point_injective (hk0 : 0 < start + j) :
    Function.Injective (terminalSecondComponent hπ data D j hj hk0 hk hp) := by
  apply ProjectiveLine.map_injective_of_parameter_pullback
    (terminalSecondComponent hπ data D j hj hk0 hk hp) (E) (𝟙 _)
    (terminalConicSecondParameter hπ data D j hj hk0 hk)
    (terminalConicFirstBranch hπ data D j hj hk hp)
  · exact Function.injective_id
  · unfold terminalConicSecondParameter
    exact Scheme.Hom.injective _
  · unfold terminalConicFirstBranch
    exact Scheme.Hom.injective _
  · exact terminalSecondComponent_left hπ data D j hj hk0 hk hp
  · simpa only [Category.id_comp] using
      terminalSecondComponent_right hπ data D j hj hk0 hk hp
  · rw [Category.comp_id, conicZeroAffineIso_puncture]
    exact terminalConicSecondParameter_isPullback hπ data D j hj hk0 hk hp

/-- The complete first terminal component is injective on all scheme points. -/
theorem terminalZeroFirstComponent_point_injective (hk0 : start + j = 0) :
    Function.Injective (terminalZeroFirstComponent hπ data D j hj hk0 hk hp) := by
  apply ProjectiveLine.map_injective_of_parameter_pullback
    (terminalZeroFirstComponent hπ data D j hj hk0 hk hp) (E) (𝟙 _)
    (terminalZeroConicFirstParameter hπ data D j hj hk0 hk)
    (terminalConicSecondBranch hπ data D j hj hk hp)
  · exact Function.injective_id
  · unfold terminalZeroConicFirstParameter
    exact Scheme.Hom.injective _
  · unfold terminalConicSecondBranch
    exact Scheme.Hom.injective _
  · exact terminalZeroFirstComponent_left hπ data D j hj hk0 hk hp
  · simpa only [Category.id_comp] using
      terminalZeroFirstComponent_right hπ data D j hj hk0 hk hp
  · rw [Category.comp_id, conicZeroAffineIso_puncture]
    exact terminalZeroConicFirstParameter_isPullback hπ data D j hj hk0 hk hp

/-- The complete second terminal component is injective on all scheme points. -/
theorem terminalZeroSecondComponent_point_injective (hk0 : start + j = 0) :
    Function.Injective (terminalZeroSecondComponent hπ data D j hj hk0 hk hp) := by
  apply ProjectiveLine.map_injective_of_parameter_pullback
    (terminalZeroSecondComponent hπ data D j hj hk0 hk hp) (E) (𝟙 _)
    (terminalZeroConicSecondParameter hπ data D j hj hk0 hk)
    (terminalConicFirstBranch hπ data D j hj hk hp)
  · exact Function.injective_id
  · unfold terminalZeroConicSecondParameter
    exact Scheme.Hom.injective _
  · unfold terminalConicFirstBranch
    exact Scheme.Hom.injective _
  · exact terminalZeroSecondComponent_left hπ data D j hj hk0 hk hp
  · simpa only [Category.id_comp] using
      terminalZeroSecondComponent_right hπ data D j hj hk0 hk hp
  · rw [Category.comp_id, conicZeroAffineIso_puncture]
    exact terminalZeroConicSecondParameter_isPullback hπ data D j hj hk0 hk hp

end FLT.Mazur.WeierstrassDividedDepth
