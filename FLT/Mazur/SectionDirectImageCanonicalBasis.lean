/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NeutralTwistDirectImage
public import FLT.Mazur.SectionDivisorLeadingSections

/-!
# Canonical bases from an invertible section adjunction

An invertible ordinary section adjunction gives an H0 basis whose vector is
exactly that section. The power-one tensor unitor retains the same vector.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules Module
namespace FLT.Mazur.FCurve.SectionAdjunction
open ModuleLineBundleTensorPullback ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor

variable {X S : Scheme} (f : X ⟶ S) (L : X.Modules) (s : Γ(L, ⊤))

/-- The ordinary adjoint takes the base unit to the specified total-space section. -/
theorem unit_section : (sectionDirectImageMap f L s).app ⊤ (1 : Γ(S, ⊤)) = s := by
  change (globalSectionHom L s).app (f ⁻¹ᵁ ⊤)
    ((modulePullbackUnitIso f).hom.app (f ⁻¹ᵁ ⊤)
      (((pullbackPushforwardAdjunction f).unit.app (structureModule S)).app ⊤ (1 : Γ(S, ⊤)))) = s
  rw [modulePullbackUnitIso_unit, map_one]
  exact globalSectionHom_top L s

variable [IsIso (sectionDirectImageMap f L s)]

/-- Coefficients with respect to the specified section and its actual adjunction. -/
def coefficient : ModuleRingH f.appTop.hom L 0 ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤) :=
  (ringHZeroPushforwardSections f L).trans
    (((AffineModuleGlobalSections.sections S).mapIso
      (asIso (sectionDirectImageMap f L s)).symm).toLinearEquiv)

/-- The inverse coefficient retains the original section, without an arbitrary scalar. -/
theorem coefficient_symm_one :
    ringHZeroPushforwardSections f L ((coefficient f L s).symm 1) = s := by
  change ringHZeroPushforwardSections f L
    ((ringHZeroPushforwardSections f L).symm
      ((sectionDirectImageMap f L s).app ⊤ (1 : Γ(S, ⊤)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact unit_section f L s

/-- The normalized singleton H0 basis. -/
def basis : Basis Unit Γ(S, ⊤) (ModuleRingH f.appTop.hom L 0) :=
  (Basis.singleton Unit Γ(S, ⊤)).map (coefficient f L s).symm

/-- The unique basis vector is the specified original section. -/
theorem basis_section : ringHZeroPushforwardSections f L (basis f L s ()) = s := by
  rw [basis, Basis.map_apply, Basis.singleton_apply]
  exact coefficient_symm_one f L s

/-- Transport the normalized basis to the actual first tensor power. -/
def powerOneBasis : Basis Unit Γ(S, ⊤)
    (ModuleRingH f.appTop.hom (tensorPower L 1) 0) :=
  (basis f L s).map
    (((moduleRingHFunctor f.appTop.hom 0).mapIso (rightUnitor L).symm).toLinearEquiv)

/-- The power-one unitor carries the vector to exactly the original section. -/
theorem powerOneBasis_section :
    (rightUnitor L).hom.app ⊤ (moduleH0Equiv _ (powerOneBasis f L s ())) = s := by
  rw [powerOneBasis, Basis.map_apply]
  change (rightUnitor L).hom.app ⊤
    (moduleH0Equiv _ (moduleHMap (rightUnitor L).inv 0 (basis f L s ()))) = _
  rw [moduleH0Equiv_naturality]
  have he := ConcreteCategory.congr_hom (congrArg (fun a ↦ a.app ⊤)
    (rightUnitor L).inv_hom_id)
  exact (he _).trans (basis_section f L s)

end FLT.Mazur.FCurve.SectionAdjunction
