/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOpenEnvelopeInterior

/-!
# The maximal source open whose entire fiber lies in a prescribed open

Remove the closure of the image of the complement. This works without
properness, but a point whose fiber lies in the given open need not survive
that closure. The construction retains that precise coverage obligation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeOpenEnvelope
variable {Y X : Scheme} (f : Y ⟶ X) (O : Y.Opens)

/-- Membership excludes the closure of the image of the bad locus, not just the image. -/
theorem mem_fullFiberInterior (x : X) :
    x ∈ fullFiberInterior f O ↔ x ∉ closure (f '' (O : Set Y)ᶜ) := by
  change x ∈ interior (f '' (O : Set Y)ᶜ)ᶜ ↔ _
  rw [interior_compl]
  rfl

/-- A test over this source open factors through the entire prescribed relation open. -/
def fullFiberInteriorTestLift {T : Scheme} (g : T ⟶ Y)
    (hg : Set.range (g ≫ f) ⊆ fullFiberInterior f O) : T ⟶ O.toScheme :=
  IsOpenImmersion.lift O.ι g (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    apply preimage_fullFiberInterior_le f O
    exact hg ⟨t, rfl⟩)

/-- The factorization keeps the original scheme morphism. -/
@[reassoc] theorem fullFiberInteriorTestLift_inclusion {T : Scheme} (g : T ⟶ Y)
    (hg : Set.range (g ≫ f) ⊆ fullFiberInterior f O) :
    fullFiberInteriorTestLift f O g hg ≫ O.ι = g := IsOpenImmersion.lift_fac _ _ _

/-- Closedness of the bad image is sufficient to retain every already-good full fiber. -/
theorem mem_fullFiberInterior_of_isClosed_image (hclosed : IsClosed (f '' (O : Set Y)ᶜ))
    (x : X) (hx : ∀ y : Y, f y = x → y ∈ O) : x ∈ fullFiberInterior f O := by
  rw [mem_fullFiberInterior, hclosed.closure_eq]
  rintro ⟨y, hy, hxy⟩
  exact hy (hx y hxy)

end FLT.Mazur.SchemeOpenEnvelope
