/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Flattening an isomorphism in an open Cartesian square

An isomorphism between open charts identifies the restriction of the original
morphism to the image of the target chart. The inverse retains the original
source inclusion, so this construction can be used on nested neighborhoods.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartesianOpenIsoRestriction

variable {A B X Y : Scheme} (e : A ⟶ B) (a : A ⟶ X) (b : B ⟶ Y) (f : X ⟶ Y)
  [IsOpenImmersion a] [IsOpenImmersion b] (H : IsPullback e a b f)

include H in
/-- The source chart is the full inverse image of the target chart. -/
theorem source_range : a.opensRange = f ⁻¹ᵁ b.opensRange := by
  simpa using IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H ⊤

/-- Identify the original source chart with the flattened inverse image. -/
def sourceIso : A ≅ (f ⁻¹ᵁ b.opensRange).toScheme :=
  IsOpenImmersion.isoOfRangeEq a (f ⁻¹ᵁ b.opensRange).ι (by
    rw [Scheme.Opens.range_ι, ← source_range e a b f H]
    rfl)

/-- The flattened source identification retains its original inclusion. -/
@[reassoc] theorem sourceIso_hom_inclusion :
    (sourceIso e a b f H).hom ≫ (f ⁻¹ᵁ b.opensRange).ι = a :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The original restricted map is the original chart comparison under these identifications. -/
theorem restrict_eq :
    f ∣_ b.opensRange = (sourceIso e a b f H).inv ≫ e ≫ b.isoOpensRange.hom := by
  apply (cancel_mono b.opensRange.ι).mp
  rw [morphismRestrict_ι, Category.assoc, Category.assoc,
    Scheme.Hom.isoOpensRange_hom_ι, H.w, ← Category.assoc]
  exact congrArg (fun k => k ≫ f)
    (IsOpenImmersion.isoOfRangeEq_inv_fac a (f ⁻¹ᵁ b.opensRange).ι _).symm

include H in
/-- An isomorphism on nested open charts is an isomorphism on the actual target open. -/
theorem isIso_restrict [IsIso e] : IsIso (f ∣_ b.opensRange) := by
  rw [restrict_eq e a b f H]
  infer_instance

end FLT.Mazur.CartesianOpenIsoRestriction
