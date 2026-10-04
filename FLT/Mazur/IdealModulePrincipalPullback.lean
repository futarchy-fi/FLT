/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealModulePullbackRestrict
public import FLT.Mazur.ModuleGlobalUnitGenerator
public import FLT.Mazur.RelativeCartierBaseChange

/-!
# The canonical ideal comparison on principal Cartier charts

A regular equation and its regular image generate the actual ideal sheaves.
The canonical pullback comparison carries one generator to the other, so it
is invertible. This uses no flatness of the ambient morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}}

/-- A section whose image is a regular generator generates the whole ideal sheaf. -/
lemma idealGlobalSection_isIso [IsAffine X] (I : X.IdealSheafData)
    (a : Γ(X, ⊤)) (ha : IsRegular a)
    (hI : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {a})
    (s : Γ(idealModule I, ⊤)) (hs : (idealModuleι I).app ⊤ s = a) :
    IsIso (globalSectionHom (idealModule I) s) := by
  let h : CartierChart I ⟨⊤, isAffineOpen_top X⟩ := ⟨a, ha, hI⟩
  let e := CartierModule.idealEquiv _ a ha hI
  let c := (idealModuleAffineEquiv I ⟨⊤, isAffineOpen_top X⟩).trans e.symm
  apply globalSectionHom_isIso_of_linear_coordinate (idealModule I)
    (trivializationOfTop _ h.idealTrivialization) c s
  have he : idealModuleAffineEquiv I ⟨⊤, isAffineOpen_top X⟩ s = e 1 := by
    apply Subtype.ext
    rw [idealModuleAffineEquiv_val, hs]
    simp [e]
  have hc : c s = 1 := by
    change e.symm (idealModuleAffineEquiv I ⟨⊤, isAffineOpen_top X⟩ s) = 1
    rw [he, e.symm_apply_apply]
  rw [hc]
  exact isUnit_one

/-- If a principal Cartier equation stays regular, the canonical ideal map is invertible. -/
theorem idealModulePullbackHom_isIso_principal [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) (a : Γ(Y, ⊤)) (ha : IsRegular a)
    (hI : I.ideal ⟨⊤, isAffineOpen_top Y⟩ = Ideal.span {a})
    (hf : IsRegular (f.appTop a)) : IsIso (idealModulePullbackHom I f) := by
  let s := (idealModuleAffineEquiv I ⟨⊤, isAffineOpen_top Y⟩).symm
    (CartierModule.idealEquiv _ a ha hI 1)
  have hs : (idealModuleι I).app ⊤ s = a := by
    rw [← idealModuleAffineEquiv_val I ⟨⊤, isAffineOpen_top Y⟩]
    simp [s]
  have : IsIso (globalSectionHom (idealModule I) s) := idealGlobalSection_isIso I a ha hI s hs
  have hp : IsIso (globalSectionHom ((pullback f).obj (idealModule I))
      (pullGlobal f (idealModule I) s)) := by
    rw [globalSectionHom_pullGlobal]
    infer_instance
  have ht : (idealModuleι (I.comap f)).app ⊤
      ((idealModulePullbackHom I f).app ⊤ (pullGlobal f (idealModule I) s)) = f.appTop a := by
    change (idealModuleι (I.comap f)).app (f ⁻¹ᵁ ⊤)
      ((idealModulePullbackHom I f).app (f ⁻¹ᵁ ⊤)
        (((pullbackPushforwardAdjunction f).unit.app _).app ⊤ s)) = _
    rw [idealModulePullbackHom_unit, hs]
    rfl
  have hJ : (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {f.appTop a} := by
    rw [Scheme.IdealSheafData.ideal_comap_top, hI, Ideal.map_span, Set.image_singleton]
  have := idealGlobalSection_isIso (I.comap f) _ hf hJ _ ht
  have : IsIso (globalSectionHom ((pullback f).obj (idealModule I))
      (pullGlobal f (idealModule I) s) ≫ idealModulePullbackHom I f) := by
    rw [globalSectionHom_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (globalSectionHom _ (pullGlobal f (idealModule I) s)) _

/-- Relative flatness of the divisor suffices on affine principal charts. -/
theorem idealModulePullbackHom_isIso_affine_relative {S T : Scheme.{u}}
    [IsAffine X] [IsAffine S] [IsAffine T] (f : X ⟶ S) (g : T ⟶ S)
    (I : X.IdealSheafData) [Flat (I.subschemeι ≫ f)]
    (hI : CartierChart I ⟨⊤, isAffineOpen_top X⟩) :
    IsIso (idealModulePullbackHom I (CategoryTheory.Limits.pullback.fst f g)) := by
  obtain ⟨a, ha, hIa⟩ := hI
  exact idealModulePullbackHom_isIso_principal I _ a ha hIa
    (isRegular_pullback_fst_appTop f g I a ha hIa)

end FLT.Mazur.FCurve
