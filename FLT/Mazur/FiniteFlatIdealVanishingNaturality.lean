/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatIdealVanishingBaseChange

/-!
# Global base change of the coefficient ideal sheaf

Compatible affine charts cover every base change. Their exact ideal
equalities therefore identify the global coefficient sheaves, including
nonflat base changes and nonreduced bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteFlatIdealVanishing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {D E S T : Scheme} {g : D ⟶ S} {q : E ⟶ T} {i : E ⟶ D} {f : T ⟶ S}
  [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
  [IsFinite q] [Flat q] [LocallyOfFinitePresentation q]
  (H : IsPullback i q g f) (J : D.IdealSheafData)

include H in
/-- The actual global coefficient ideal commutes with arbitrary geometric base change. -/
theorem idealSheaf_baseChange :
    idealSheaf q (J.comap i) = (idealSheaf g J).comap f := by
  let C := Σ V : S.affineOpens, {U : T.affineOpens // U.1 ≤ f ⁻¹ᵁ V.1}
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top (fun c : C ↦ c.2.1)
  · apply top_unique
    intro x _
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open hxV (f ⁻¹ᵁ V).isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, ⟨⟨U, hU⟩, hUV⟩⟩, hxU⟩
  · intro c
    exact idealSheaf_baseChange_ideal H J c.1 c.2.1 c.2.2

/-- The pullback family locus maps canonically to the original global closed locus. -/
def locusMap : locus q (J.comap i) ⟶ locus g J :=
  Scheme.IdealSheafData.subschemeMap (idealSheaf q (J.comap i)) (idealSheaf g J) f
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr (idealSheaf_baseChange H J).ge)

/-- The locus comparison preserves the original base map. -/
@[reassoc (attr := simp)] theorem locusMap_inclusion :
    locusMap H J ≫ locusInclusion g J = locusInclusion q (J.comap i) ≫ f :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The global closed locus itself commutes with arbitrary geometric base change. -/
theorem locus_isPullback :
    IsPullback (locusInclusion q (J.comap i)) (locusMap H J) f (locusInclusion g J) := by
  apply isPullback_of_isClosedImmersion
  · exact (locusMap_inclusion H J).symm
  · change (idealSheaf g J).subschemeι.ker.comap f =
      (idealSheaf q (J.comap i)).subschemeι.ker
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
    exact (idealSheaf_baseChange H J).symm

end FLT.Mazur.FiniteFlatIdealVanishing
