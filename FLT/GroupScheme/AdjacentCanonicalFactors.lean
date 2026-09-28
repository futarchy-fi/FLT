/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.IntegralExtensionComposition
public import FLT.GroupScheme.IntegralExtensionPullback
public import FLT.GroupScheme.ReverseExtSwappedExtension

/-!
# Adjacent interchange of canonical integral factors

Quotient by the inner kernel, split and reverse the resulting pair, then pull
its multiplicative subgroup back to the original middle model. The resulting
sequences are full integral extensions, including faithful flatness and torsors.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- Move a multiplicative factor below an adjacent constant factor inside an
arbitrary integral filtration while retaining its original bottom and top models. -/
theorem swapAdjacentFactors {A B H : FiniteFlatObject ZInvTwo}
    (E₁ : FiniteFlatExtension A B constantThree)
    (E₂ : FiniteFlatExtension B H muThree) :
    ∃ B' : FiniteFlatObject ZInvTwo,
      Nonempty (FiniteFlatExtension A B' muThree) ∧
      Nonempty (FiniteFlatExtension B' H constantThree) := by
  obtain ⟨T, E, F, _, _, _⟩ := composeIntegralExtensionsCompatible E₁ E₂
  exact pullbackIntegralExtensions E F.existsSwappedExtension.some

end ThreeAdicPlan
