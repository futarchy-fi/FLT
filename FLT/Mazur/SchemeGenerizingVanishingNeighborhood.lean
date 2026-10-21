/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NoetherianClosedImageGenerizations
public import FLT.Mazur.SchemeAdicVanishingOpen

/-!
# Constructed target neighborhoods from all generizing zero germs

For a Noetherian source, every point in the closure of a closed-set image is
witnessed by an actual source point over a generization. Thus full zero-germ
tests over all generizations construct a target neighborhood. No closedness
of the morphism or reducedness of the section is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeAdicVanishingNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme} [NoetherianSpace X] (f : X ⟶ Y) (a : Γ(X, ⊤))

/-- Germs on the whole generizing fiber construct a genuine target vanishing neighborhood. -/
theorem exists_target_neighborhood_of_generizing_germs (y : Y)
    (hy : ∀ x : X, f x ⤳ y → X.presheaf.germ ⊤ x (by trivial) a = 0) :
    ∃ V : Y.Opens, y ∈ V ∧
      X.presheaf.map (homOfLE le_top : f ⁻¹ᵁ V ⟶ ⊤).op a = 0 := by
  let V : Y.Opens :=
    ⟨(closure (f '' (vanishingOpen a : Set X)ᶜ))ᶜ, isClosed_closure.isOpen_compl⟩
  refine ⟨V, ?_, ?_⟩
  · intro hc
    obtain ⟨x, hx, hxy⟩ := (NoetherianClosedImage.mem_closure_image_iff f f.continuous
      (vanishingOpen a).isOpen.isClosed_compl y).mp hc
    exact hx (hy x hxy)
  · apply TopCat.Presheaf.section_ext X.sheaf
    intro x hx
    change X.presheaf.germ (f ⁻¹ᵁ V) x hx
      (X.presheaf.map (homOfLE le_top : f ⁻¹ᵁ V ⟶ ⊤).op a) =
        X.presheaf.germ (f ⁻¹ᵁ V) x hx 0
    rw [map_zero, X.presheaf.germ_res_apply]
    by_contra hn
    exact hx (subset_closure ⟨x, hn, rfl⟩)

/-- Actual all-order discrepancies on a supported generizing fiber yield a target neighborhood. -/
theorem exists_target_neighborhood_of_adic_generizations [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (ha : ∀ (U : X.affineOpens) (n : ℕ),
      X.presheaf.map (homOfLE le_top : U.1 ⟶ ⊤).op a ∈ I.ideal U ^ (n + 1))
    (y : Y) (hy : ∀ x : X, f x ⤳ y → x ∈ I.support) :
    ∃ V : Y.Opens, y ∈ V ∧
      X.presheaf.map (homOfLE le_top : f ⁻¹ᵁ V ⟶ ⊤).op a = 0 := by
  apply exists_target_neighborhood_of_generizing_germs f a y
  intro x hx
  exact germ_eq_zero_of_adic a I ha x (hy x hx)

end FLT.Mazur.SchemeAdicVanishingNeighborhood
