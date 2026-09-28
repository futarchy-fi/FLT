/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CategoryDPointCharacters
public import FLT.GroupScheme.CyclotomicModelIdentification

/-!
# Integral models of simple category-D objects under the discriminant bound

The generic character classification and integral order-three identification
combine to give actual bialgebra equivalences with the constant or cube-root
models. The augmented discriminant estimate remains an explicit hypothesis.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- Conditional on the augmented discriminant bound, a simple category-D object
is integrally isomorphic to the constant-three or cube-root model. -/
theorem Simple.integral_model_of_discriminantBound
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H)
    (hdisc : AugmentedDiscriminantBound H) :
    Nonempty (H.Iso constantThree) ∨ Nonempty (H.Iso muThree) := by
  let := hs.threeModule hD
  obtain ⟨hdim, χ, hχ, hact⟩ := hs.point_character_of_discriminantBound hD hdisc
  rcases hχ with hχ | hχ
  · subst χ
    obtain ⟨i, _⟩ := exists_iso_constantThree H hdim (fun σ x ↦ by simpa using hact σ x)
    exact Or.inl ⟨i⟩
  · subst χ
    exact Or.inr (exists_iso_muThree H hdim hact)

end ThreeAdicPlan
