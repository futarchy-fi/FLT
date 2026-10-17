/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAdicVanishingNeighborhood

/-!
# The actual open on which an adically vanishing section is zero

The definition uses zero germs in the structure sheaf, so nilpotents are
retained. Local noetherian separation places the whole adic support in this
open, and the original section restricts to zero on the open itself.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeAdicVanishingNeighborhood
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme} (a : Γ(X, ⊤))

/-- The zero-germ locus is an actual open, without reducedness assumptions. -/
theorem isOpen_zero_germs :
    IsOpen {x : X | X.presheaf.germ ⊤ x (by trivial) a = 0} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨V, i, hxV, hV⟩ :=
    X.toRingedSpace.exists_res_eq_zero_of_germ_eq_zero ⊤ a ⟨x, by trivial⟩ hx
  refine ⟨V, ?_, V.isOpen, hxV⟩
  intro y hy
  change X.presheaf.germ ⊤ y _ a = 0
  rw [← X.presheaf.germ_res_apply i y hy, hV, map_zero]

/-- The largest open where the original section vanishes scheme-theoretically. -/
def vanishingOpen : X.Opens :=
  ⟨{x : X | X.presheaf.germ ⊤ x (by trivial) a = 0}, isOpen_zero_germs a⟩

/-- The actual original section is zero on this open, including its nilpotent part. -/
theorem vanishingOpen_restrict :
    X.presheaf.map (homOfLE le_top : vanishingOpen a ⟶ ⊤).op a = 0 := by
  apply TopCat.Presheaf.section_ext X.sheaf
  intro x hx
  change X.presheaf.germ (vanishingOpen a) x hx
    (X.presheaf.map (homOfLE le_top : vanishingOpen a ⟶ ⊤).op a) =
      X.presheaf.germ (vanishingOpen a) x hx 0
  rw [map_zero, X.presheaf.germ_res_apply]
  exact hx

/-- Pullback to the actual open subscheme kills the original section. -/
theorem vanishingOpen_inclusion_zero : (vanishingOpen a).ι.appTop a = 0 := by
  have h := congrArg (fun z ↦ (vanishingOpen a).topIso.inv z) (vanishingOpen_restrict a)
  rw [map_zero] at h
  change (X.presheaf.map _ ≫ X.presheaf.map _) a = 0 at h
  rw [← X.presheaf.map_comp] at h
  exact h

/-- Every open on which the section is zero factors into the constructed vanishing open. -/
theorem le_vanishingOpen (V : X.Opens)
    (hV : X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op a = 0) :
    V ≤ vanishingOpen a := by
  intro x hx
  change X.presheaf.germ ⊤ x _ a = 0
  rw [← X.presheaf.germ_res_apply (homOfLE le_top : V ⟶ ⊤) x hx, hV, map_zero]

/-- All-order membership kills every actual germ on the adic support. -/
theorem germ_eq_zero_of_adic [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (ha : ∀ (V : X.affineOpens) (n : ℕ),
      X.presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op a ∈ J.ideal V ^ (n + 1))
    (x : X) (hx : x ∈ J.support) : X.presheaf.germ ⊤ x (by trivial) a = 0 := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨s, _, hs, hz⟩ := exists_affine_neighborhood J ⟨V, hV⟩ _ (ha ⟨V, hV⟩)
  have hxs := hs ⟨hx, hxV⟩
  have h := congrArg ((X.presheaf.germ (X.basicOpen s) x hxs).hom) hz
  simpa only [TopCat.Presheaf.germ_res_apply, map_zero] using h

/-- The full closed support lies in an actual ambient open where the section is zero. -/
theorem support_subset_vanishingOpen [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (ha : ∀ (V : X.affineOpens) (n : ℕ),
      X.presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op a ∈ J.ideal V ^ (n + 1)) :
    (J.support : Set X) ⊆ vanishingOpen a :=
  germ_eq_zero_of_adic a J ha

end FLT.Mazur.SchemeAdicVanishingNeighborhood
