/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafClosedTransitions
public import FLT.Mazur.SchemeEffectiveEpiSections

/-!
# Full boundary equations detected on an original open cover

Pulling the cover back through the actual ideal subscheme gives a cover of
its full structure sheaf. Consequently a glued ambient coefficient retains
prescribed boundary values whenever its local coefficients do. This uses the
unchanged ideal, not its radical or any set-theoretic zero locus.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OpenCoverFullBoundaryDetection
open IdealSheafClosedTransitions SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{0}} {ι : Type} (U : ι → X.Opens) (hcover : iSup U = ⊤)
  (I : X.IdealSheafData)

include hcover in
/-- The actual pulled boundary maps jointly detect full boundary sections. -/
theorem boundary_ext (s t : Γ(I.subscheme, ⊤))
    (h : ∀ i, (map (I.comap (U i).ι) I (U i).ι rfl).appTop s =
      (map (I.comap (U i).ι) I (U i).ι rfl).appTop t) : s = t := by
  let C := X.openCoverOfIsOpenCover U hcover
  apply Scheme.OpenCover.ext_elem s t (C.pullback₂ I.subschemeι)
  intro i
  apply appTop_injective (I.comapIso (U i).ι).hom
  change ((I.comapIso (U i).ι).hom ≫ pullback.snd (U i).ι I.subschemeι).appTop s =
    ((I.comapIso (U i).ι).hom ≫ pullback.snd (U i).ι I.subschemeι).appTop t
  rw [Scheme.IdealSheafData.comapIso_hom_snd]
  exact h i

include hcover in
/-- Local boundary values of any glued coefficient give its full global boundary value. -/
theorem boundary_eq_of_local (s : Γ(X, ⊤)) (t : Γ(I.subscheme, ⊤))
    (h : ∀ i, (I.comap (U i).ι).subschemeι.appTop ((U i).ι.appTop s) =
      (map (I.comap (U i).ι) I (U i).ι rfl).appTop t) :
    I.subschemeι.appTop s = t := by
  apply boundary_ext U hcover I
  intro i
  rw [← section_square]
  exact h i

include hcover in
/-- Full homogeneous boundary conditions survive gluing, including nilpotents. -/
theorem boundary_zero_of_local (s : Γ(X, ⊤))
    (h : ∀ i, (I.comap (U i).ι).subschemeι.appTop ((U i).ι.appTop s) = 0) :
    I.subschemeι.appTop s = 0 := by
  apply boundary_eq_of_local U hcover I s 0
  intro i
  rw [map_zero]
  exact h i

end FLT.Mazur.OpenCoverFullBoundaryDetection
