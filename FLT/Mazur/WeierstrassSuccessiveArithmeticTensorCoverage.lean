/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveArithmeticBoundaryCoverage

/-!
# Both labels cover the full original arithmetic tensor algebra

The two constructed branches retain their actual tensor comparison. No
localization or reduction of the quotient coefficients is made in this cover.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonArithmeticStages
variable {R : Type} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m

/-- After any further scheme map, the two labeled images are exactly the original chart image. -/
theorem arithmeticTensorBranches_image {X : Scheme}
    (f : Spec (.of (ScalarExtension W s π b3 b4 b6 Q)) ⟶ X) :
    Set.range (arithmeticTensorBranchChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6 false ≫ f) ∪
      Set.range (arithmeticTensorBranchChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6 true ≫ f) =
        Set.range f := by
  apply Set.Subset.antisymm
  · rintro _ (⟨z, rfl⟩ | ⟨z, rfl⟩)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · rintro _ ⟨z, rfl⟩
    obtain ⟨label, x, rfl⟩ :=
      arithmeticTensorBranches_cover π m W s b3 b4 b6 ha hs h2 h3 h4 h6 z
    cases label
    · exact Or.inl ⟨x, rfl⟩
    · exact Or.inr ⟨x, rfl⟩

end FLT.Mazur.WeierstrassSuccessiveX
