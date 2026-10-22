/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothOpenSectionCartier

/-!
# Cartier markings from a relative-curve neighborhood

A section contained in a relative-dimension-one open cuts out a relative
Cartier divisor on the whole separated family. No flatness or smoothness
of the whole family is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
universe u
set_option backward.isDefEq.respectTransparency false

/-- A dimension-one neighborhood makes the original whole-family section Cartier. -/
theorem relativeCartier_of_section_neighborhood {X S : Scheme.{u}}
    (p : X ⟶ S) [IsSeparated p] (t : S ⟶ X) (ht : t ≫ p = 𝟙 _)
    (V : X.Opens) (hV : t ⁻¹ᵁ V = ⊤) [SmoothOfRelativeDimension 1 (V.ι ≫ p)] :
    RelativeEffectiveCartier p t.ker := by
  have hr : Set.range t ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hV.ge (Set.mem_univ x)
  let s := IsOpenImmersion.lift V.ι t hr
  have hs : s ≫ V.ι = t := IsOpenImmersion.lift_fac _ _ _
  have hsp : s ≫ V.ι ≫ p = 𝟙 _ := by rw [← Category.assoc, hs, ht]
  have h := smoothOpenSectionCartier V.ι p s inferInstance inferInstance inferInstance hsp
  rwa [hs] at h

end FLT.Mazur.FCurve
