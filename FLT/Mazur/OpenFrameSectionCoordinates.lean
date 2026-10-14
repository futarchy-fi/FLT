/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPullbackLineCoordinate
public import FLT.Mazur.DivisorFrameIdeal

/-!
# Linear coordinates from actual open-chart frames

A frame on an open immersion gives a linear frame on the original image-open
sections. Its scalar coordinate agrees with genuine pullback of global sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
  (M : Y.Modules) (e : M.restrict f ≅ structureModule X)

/-- An actual open-chart frame, in the original image-open section ring. -/
def openFrameLinearEquiv : Γ(M, f ''ᵁ ⊤) ≃ₗ[Γ(Y, f ''ᵁ ⊤)] Γ(Y, f ''ᵁ ⊤) :=
  LinearEquiv.ofBijective
    { toFun := fun s => (f.appIso ⊤).inv
        (e.hom.app ⊤ ((M.restrictAppIso f ⊤).inv s))
      map_add' := fun s t => by simp only [map_add]
      map_smul' := fun r s => by
        erw [M.smul_restrictAppIso_inv_apply f ⊤ r s, Hom.app_smul]
        change (f.appIso ⊤).inv ((f.appIso ⊤).hom r * _) = r * _
        rw [map_mul, Iso.hom_inv_id_apply] }
    ((ConcreteCategory.bijective_of_isIso (f.appIso ⊤).inv).comp
      ((ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).comp
        (ConcreteCategory.bijective_of_isIso (M.restrictAppIso f ⊤).inv)))

/-- The same frame on the genuine pulled module. -/
def openFramePullback : (pullback f).obj M ≅ structureModule X :=
  ((restrictFunctorIsoPullback f).app M).symm ≪≫ e

/-- Scalar pullback of the original coordinate is the genuine pulled line coordinate. -/
theorem openFrameLinearEquiv_pullGlobal (s : Γ(M, ⊤)) :
    (f.appIso ⊤).hom (openFrameLinearEquiv f M e
      (M.presheaf.map (homOfLE (show f ''ᵁ ⊤ ≤ ⊤ from le_top)).op s)) =
        pulledLineCoordinate f M (openFramePullback f M e) s := by
  rw [pulledLineCoordinate_def, ← pullGlobal_restrict]
  change (f.appIso ⊤).hom ((f.appIso ⊤).inv (e.hom.app ⊤ _)) =
    e.hom.app ⊤ (((restrictFunctorIsoPullback f).inv.app M).app ⊤
      (((restrictFunctorIsoPullback f).hom.app M).app ⊤ _))
  rw [Iso.inv_hom_id_apply]
  have he := congrArg (fun a => a.app ⊤
    (M.presheaf.map (homOfLE (show f ''ᵁ ⊤ ≤ ⊤ from le_top)).op s))
      ((restrictFunctorIsoPullback f).hom_inv_id_app M)
  exact congrArg (e.hom.app ⊤) he.symm

/-- A Cartier frame retains the full ideal of the original canonical section. -/
theorem divisorSection_openFrame_span (I : Y.IdealSheafData) (hI : EffectiveCartier I)
    (e : (divisorLineBundle I hI).restrict f ≅ structureModule X)
    (hA : IsAffineOpen (f ''ᵁ ⊤)) (hC : CartierChart I ⟨f ''ᵁ ⊤, hA⟩) :
    Ideal.span {(pulledLineCoordinate f (divisorLineBundle I hI)
      (openFramePullback f _ e) (divisorSection hI ⊤))} =
        Ideal.map (f.appIso ⊤).hom.hom (I.ideal ⟨f ''ᵁ ⊤, hA⟩) := by
  rw [← openFrameLinearEquiv_pullGlobal, divisorSection_restrict]
  rw [← divisorSection_span_in_frame hI hC (openFrameLinearEquiv f _ e),
    Ideal.map_span, Set.image_singleton]

end FLT.Mazur.FCurve
