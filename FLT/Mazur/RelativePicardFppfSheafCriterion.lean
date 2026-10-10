/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardFppfCover
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# An fppf sheaf criterion on test schemes

It suffices to check the original base-cover arrows. Every small cover in the
slice is isomorphic, member by member, to one of these specified families.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u v
namespace FLT.Mazur.SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v)

/-- Original base-cover sheaf conditions imply sheafness on the full fppf slice site. -/
theorem relativeFppf_isSheaf_of_families
    (h : ∀ (T : Over S) (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage T.left),
      Presieve.IsSheafFor F
        (Presieve.ofArrows (relativeCoverMember T 𝒰) (relativeCoverArrow T 𝒰))) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) F := by
  let _ : Precoverage.Small.{u} Scheme.fppfPrecoverage := by
    unfold Scheme.fppfPrecoverage
    infer_instance
  rw [isSheaf_iff_isSheaf_of_type, Scheme.fppfTopology,
    over_toGrothendieck_eq_toGrothendieck_comap_forget]
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small.{u}]
  intro T E
  let 𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage T.left :=
    E.map (Over.forget S) le_rfl
  let e (i : E.I₀) : relativeCoverMember T 𝒰 i ≅ E.X i :=
    Over.isoMk (Iso.refl _) (by
      change (𝟙 (E.X i).left) ≫ (E.X i).hom = (E.f i).left ≫ T.hom
      rw [Category.id_comp, Over.w])
  have he (i : E.I₀) : (e i).hom ≫ E.f i = relativeCoverArrow T 𝒰 i := by
    apply Over.OverMorphism.ext
    exact Category.id_comp (E.f i).left
  change Presieve.IsSheafFor F (Presieve.ofArrows E.X E.f)
  rw [← Presieve.isSheafFor_ofArrows_comp_iff E.f e]
  simpa only [he] using h T 𝒰

end FLT.Mazur.SchemePicard
