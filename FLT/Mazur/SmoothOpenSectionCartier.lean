/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SmoothSectionCartier

/-!
# Sections contained in a smooth open

A section landing in the smooth open of a separated relative curve defines a
relative effective Cartier divisor on the entire curve. Its actual ideal pulls
back to the section ideal on the open, where the smooth section theorem applies.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

/-- A section lying in the smooth open is Cartier even if the ambient family is singular. -/
theorem smoothOpenSectionCartier {U X S : Scheme.{u}}
    (j : U ⟶ X) (f : X ⟶ S) (s : S ⟶ U) : SmoothOpenSectionCartier j f s := by
  intro hj hf hsep hs
  have hs' : (s ≫ j) ≫ f = 𝟙 S := by simpa only [Category.assoc] using hs
  let : IsClosedImmersion (s ≫ j) := isClosedImmersion_section f (s ≫ j) hs'
  have hpb : IsPullback s (𝟙 S) j (s ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have hker : (s ≫ j).ker.comap j = s.ker := by
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    rw [← Scheme.Hom.ker_comp_of_isIso hpb.isoPullback.hom,
      hpb.isoPullback_hom_fst]
  have hI := (smoothSectionCartier (j ≫ f) s hf inferInstance hs).1
  apply (relativeEffectiveCartier_section_iff_charts f (s ≫ j) hs').mpr
  intro y
  obtain ⟨V, hy, hV⟩ := hI (s y)
  refine ⟨⟨j ''ᵁ V, V.2.image_of_isOpenImmersion j⟩, ⟨s y, hy, rfl⟩, ?_⟩
  apply (cartierChart_comap_iff (s ≫ j).ker j V).mp
  simpa only [hker, CartierChart] using hV

end FLT.Mazur.FCurve
