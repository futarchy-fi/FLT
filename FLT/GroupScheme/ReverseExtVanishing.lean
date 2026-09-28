/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.ConstantMuThreeSplitting
public import FLT.GroupScheme.ReverseExtHypothesis

/-!
# Unconditional reverse extension vanishing

The splitting of each actual constant-three extension of the cube-root group
discharges the reverse extension hypothesis used in the filtration constructions.
The splitting retains the specified integral inclusion and quotient.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- Every constant-three extension of the cube-root group has an integral splitting. -/
theorem reverseExtVanishing : ReverseExtVanishing :=
  fun _ E ↦ ⟨E.constantThreeMuThreeModelSplitting⟩

/-- A reverse extension admits swapped integral maps with exact geometric points. -/
theorem FiniteFlatExtension.existsSwappedMaps
    {H : FiniteFlatObject ZInvTwo} (E : FiniteFlatExtension constantThree H muThree) :
    ∃ (i : muThree.Hom H) (q : H.Hom constantThree),
      i.comp q = ModelHom.zero muThree.toFF constantThree.toFF ∧
      Function.Injective (FiniteFlatObject.pointMap i) ∧
      Function.Surjective (FiniteFlatObject.pointMap q) ∧
      ∀ h : H.points, FiniteFlatObject.pointMap q h = 0 ↔
        ∃ a : muThree.points, FiniteFlatObject.pointMap i a = h :=
  reverseExtVanishing.existsSwappedMaps E

end ThreeAdicPlan
