/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenModuleSectionScalars

/-!
# Cartesian base change on affine opens of arbitrary schemes

Transport affine cartesian base change through restriction of the module sheaf.
The ambient scheme need not be affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped ChangeOfRings
universe u
namespace FLT.Mazur.AffineOpenCartesianSections
open FCurve OpenModuleSectionScalars ModulePullbackSectionCoherence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme.{u}} [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (M : X.Modules) [M.IsQuasicoherent]
  (U : X.Opens) (hU : IsAffineOpen U)

include h in
omit [IsAffine T] [IsAffine S] in
/-- Restricting the upper row of a cartesian square to an open remains cartesian. -/
lemma chartSquare : IsPullback (p ∣_ U) ((p ⁻¹ᵁ U).ι ≫ q) (U.ι ≫ f) g :=
  (isPullback_morphismRestrict p U).paste_vert h

/-- Affine-open section base change, valued in actual ambient sections. -/
def sectionsIso :
    (ModuleCat.extendScalars g.appTop.hom).obj (openSections f M U) ≅
      openSections q ((pullback p).obj M) (p ⁻¹ᵁ U) := by
  let : IsAffine U.toScheme := hU
  exact (ModuleCat.extendScalars g.appTop.hom).mapIso (chartIso f M U) ≪≫
    AffineCartesianSectionScalars.sectionsIso (chartSquare h U) (M.restrict U.ι) ≪≫
    (ModuleCat.restrictScalars ((p ⁻¹ᵁ U).ι ≫ q).appTop.hom).mapIso
      ((AffineModuleGlobalSections.sections _).mapIso (modulePullbackOpenIso p U M).symm) ≪≫
    (chartIso q ((pullback p).obj M) (p ⁻¹ᵁ U)).symm

/-- On pure tensors the transported comparison is the actual adjunction-unit map. -/
lemma sectionsIso_tmul (b : Γ(T, ⊤)) (m : Γ(M, U)) :
    (sectionsIso h M U hU).hom (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m) =
      b • (show openSections q ((pullback p).obj M) (p ⁻¹ᵁ U) from
        ((pullbackPushforwardAdjunction p).unit.app M).app U m) := by
  let : IsAffine U.toScheme := hU
  let e := chartIso q ((pullback p).obj M) (p ⁻¹ᵁ U) ≪≫
    (ModuleCat.restrictScalars ((p ⁻¹ᵁ U).ι ≫ q).appTop.hom).mapIso
      ((AffineModuleGlobalSections.sections _).mapIso (modulePullbackOpenIso p U M))
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  have he : sectionsIso h M U hU ≪≫ e =
      (ModuleCat.extendScalars g.appTop.hom).mapIso (chartIso f M U) ≪≫
        AffineCartesianSectionScalars.sectionsIso (chartSquare h U) (M.restrict U.ι) := by
    simp [sectionsIso, e]
  have ht := congrArg (fun k ↦ k.hom (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m)) he
  change e.hom ((sectionsIso h M U hU).hom _) = _ at ht
  rw [ht]
  change (AffineCartesianSectionScalars.sectionsIso (chartSquare h U)
    (M.restrict U.ι)).hom
      ((ModuleCat.extendScalars g.appTop.hom).map (chartIso f M U).hom
        (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul, AffineCartesianSectionScalars.sectionsIso_tmul,
    e.hom.hom.map_smul]
  change _ = ((p ⁻¹ᵁ U).ι ≫ q).appTop b •
    (modulePullbackOpenIso p U M).hom.app ⊤
      (chartSection ((pullback p).obj M) (p ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction p).unit.app M).app U m))
  rw [open_unit_top]
  rfl

end FLT.Mazur.AffineOpenCartesianSections
