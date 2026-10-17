/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.QuasiFiniteFppfDescent
public import FLT.Mazur.SchemeFiniteTargetRestriction

/-!
# Descending finite target neighborhoods through open flat images

A finite whole pullback over a source open descends to its open image under
any flat locally finitely presented map. This uses the entire preimage of
the original separated quasi-finite morphism, not a selected finite fiber.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P D B A : Scheme} {a : P ⟶ D} {b : P ⟶ B} {p : D ⟶ A} {g : B ⟶ A}
  (H : IsPullback a b p g) [IsSeparated p] [LocallyQuasiFinite p]
  [LocallyOfFiniteType p] [Flat g] [LocallyOfFinitePresentation g]

/-- The actual open image of a source neighborhood under a flat presentation. -/
def flatImageOpen (g : B ⟶ A) [Flat g] [LocallyOfFinitePresentation g]
    (U : B.Opens) : A.Opens := ⟨g '' U, g.isOpenMap _ U.isOpen⟩

include H in
/-- Finiteness of a whole pullback over a source open descends to its open image. -/
theorem finite_restrict_flatImage (U : B.Opens) [IsFinite (b ∣_ U)] :
    IsFinite (p ∣_ flatImageOpen g U) := by
  let O := flatImageOpen g U
  have hU : U ≤ g ⁻¹ᵁ O := fun x hx ↦ ⟨x, hx, rfl⟩
  have hP : b ⁻¹ᵁ U ≤ a ⁻¹ᵁ (p ⁻¹ᵁ O) := by
    intro x hx
    change p (a x) ∈ O
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
    exact hU hx
  have HB : IsPullback
      (a.resLE (p ⁻¹ᵁ O) (b ⁻¹ᵁ U) hP) (b ∣_ U)
      (p ∣_ O) (g.resLE O U hU) := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
      Scheme.Hom.isPullback_resLE H hU (le_rfl : p ⁻¹ᵁ O ≤ p ⁻¹ᵁ O)
        (inf_eq_right.mpr hP).symm
  let _ : Surjective (g.resLE O U hU) := ⟨by
    rintro ⟨x, y, hy, hxy⟩
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    exact (congrArg (fun t ↦ t ⟨y, hy⟩)
      (Scheme.Hom.resLE_comp_ι g hU)).trans hxy⟩
  exact finite_of_fppf_surjective_pullback HB

include H in
/-- An actual finite neighborhood upstairs supplies one at every point of its open image. -/
theorem flatImage_le_finiteTarget (U : B.Opens) [IsFinite (b ∣_ U)] :
    flatImageOpen g U ≤ finiteTargetOpen p :=
  (le_finiteTargetOpen_iff p _).mpr (finite_restrict_flatImage H U)

end FLT.Mazur.SchemeOpenEnvelope
