/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityComponentHomExt
public import FLT.Mazur.WeierstrassDividedFinalInitialParameterCharts
public import FLT.Mazur.WeierstrassDividedInitialNodeHomExt

/-!
# Cyclic component agreement on both original initial nodes

The complete original incidence line and both entire conic parameters are
recovered from component agreement. The initial two-node cover then gives
uniqueness on the full original initial atlas chart for every positive start.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (positiveEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (positiveEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

include h in
/-- Cyclic agreement determines the complete original first initial conic parameter. -/
theorem positiveEqualityCycleComponent_initial_first_parameter_hom_ext :
    initialGlobalConicFirstParameter hπ data D (s + 1) hs hstart (by omega) ≫ f =
      initialGlobalConicFirstParameter hπ data D (s + 1) hs hstart (by omega) ≫ g := by
  have H := congrArg (fun q => ProjectiveLine.left K ≫ q)
    (positiveEqualityCycleComponent_initial_hom_ext hπ data D s hs hstart hk hp f g h 0)
  simp only [finalInitialComponent_first_left_assoc] at H
  exact (cancel_epi (WeierstrassModificationX.conicZeroAffineIso _ _).hom).mp H

include h in
/-- The full original first node is determined into every target scheme. -/
theorem positiveEqualityCycleComponent_initial_first_hom_ext :
    initialGlobalResidueFirstNode hπ data D (s + 1) hs hstart (by omega) ≫ f =
      initialGlobalResidueFirstNode hπ data D (s + 1) hs hstart (by omega) ≫ g := by
  exact initialGlobalFirstNode_hom_ext hπ data D (s + 1) hs hstart (by omega) f g
    (positiveEqualityCycleComponent_incidence_hom_ext hπ data D s hs hstart hk hp f g h)
    (positiveEqualityCycleComponent_initial_first_parameter_hom_ext
      hπ data D s hs hstart hk hp f g h)

include h in
/-- Cyclic agreement determines the complete original second initial conic parameter. -/
theorem positiveEqualityCycleComponent_initial_second_parameter_hom_ext :
    initialGlobalConicSecondParameter hπ data D (s + 1) hs hstart (by omega) ≫ f =
      initialGlobalConicSecondParameter hπ data D (s + 1) hs hstart (by omega) ≫ g := by
  have H := congrArg (fun q => ProjectiveLine.left K ≫ q)
    (positiveEqualityCycleComponent_initial_hom_ext hπ data D s hs hstart hk hp f g h 1)
  simp only [finalInitialComponent_second_left_assoc] at H
  exact (cancel_epi (WeierstrassModificationX.conicZeroAffineIso _ _).hom).mp H

include h in
/-- The full original second node is determined into every target scheme. -/
theorem positiveEqualityCycleComponent_initial_second_hom_ext :
    initialGlobalResidueSecondNode hπ data D (s + 1) hs hstart (by omega) ≫ f =
      initialGlobalResidueSecondNode hπ data D (s + 1) hs hstart (by omega) ≫ g := by
  exact initialGlobalSecondNode_hom_ext hπ data D (s + 1) hs hstart (by omega) f g
    (positiveEqualityCycleComponent_incidence_hom_ext hπ data D s hs hstart hk hp f g h)
    (positiveEqualityCycleComponent_initial_second_parameter_hom_ext
      hπ data D s hs hstart hk hp f g h)

include h in
/-- The two initial node opens determine the full original last indexed atlas chart. -/
theorem positiveEqualityCycleComponent_initial_indexed_hom_ext :
    globalTensorAtlasMap hπ data K (s + 1) hs ⟨s + 3, by omega⟩ ≫ f =
      globalTensorAtlasMap hπ data K (s + 1) hs ⟨s + 3, by omega⟩ ≫ g := by
  exact initialGlobalParameters_indexed_hom_ext hπ data D (s + 1) hs hstart (by omega) f g
    (positiveEqualityCycleComponent_incidence_hom_ext hπ data D s hs hstart hk hp f g h)
    (positiveEqualityCycleComponent_initial_first_parameter_hom_ext
      hπ data D s hs hstart hk hp f g h)
    (positiveEqualityCycleComponent_initial_second_parameter_hom_ext
      hπ data D s hs hstart hk hp f g h)

end FLT.Mazur.WeierstrassDividedDepth
