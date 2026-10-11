/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementFunctions
public import FLT.Mazur.DivisorPowerHZeroTransition
public import FLT.Mazur.ModuleSectionInverseCoordinate

/-!
# Canonical pole transitions preserve the complement function

Dividing by the canonical section sends that section to one. Thus the
actual inclusions of pole spaces all represent the same regular function.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback ModuleSheafTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] divisorLineBundle sectionHom
variable {X : Scheme.{u}} {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- The inverse canonical section sends its own local restriction to one. -/
theorem divisorComplementTrivialization_canonical
    (V : (Scheme.Opens.toScheme (X := X) I.support.compl).Opens) :
    (show Γ(Scheme.Opens.toScheme (X := X) I.support.compl, V) from
      (divisorComplementTrivialization hI).hom.app V
        (((divisorLineBundle I hI).restrictAppIso
          (Scheme.Opens.ι (X := X) I.support.compl) V).inv
          (divisorSection hI ((Scheme.Opens.ι (X := X) I.support.compl) ''ᵁ V)))) = 1 := by
  let W : X.Opens := I.support.compl
  let _ := divisorSection_isIso_complement hI
  rw [divisorComplementTrivialization_def]
  change (show Γ(W.toScheme, V) from
    (inv (sectionHom (divisorLineBundle I hI) W (divisorSection hI W))).app V
      (((divisorLineBundle I hI).restrictAppIso W.ι V).inv
        (divisorSection hI (W.ι ''ᵁ V)))) = 1
  rw [← divisorSection_restrict hI (W.ι_image_le V)]
  exact inverseSectionHom_app_section _ _ _ _

/-- Prepending the canonical section leaves the actual complement function unchanged. -/
theorem divisorComplementFunction_cons (m : ℕ)
    (s : Γ(tensorPower (divisorLineBundle I hI) m, ⊤)) :
    divisorComplementFunction hI (m + 1)
      (pure _ _ ⊤ (divisorSection hI ⊤) s) = divisorComplementFunction hI m s := by
  unfold divisorComplementFunction
  dsimp only [tensorPower]
  rw [pure_restrict, divisorSection_restrict]
  change SectionGradedLocalCoordinates.coordinate _ (m + 1) ⊤
    (SectionGradedMultiplication.cons _ m _ _ _) = _
  rw [SectionGradedLocalCoordinates.coordinate_cons]
  rw [divisorComplementTrivialization_canonical, one_mul]

/-- All canonical tensor powers represent the constant function one. -/
theorem divisorComplementFunction_power (m : ℕ) :
    divisorComplementFunction hI m
      (tensorPowerSection (divisorLineBundle I hI) ⊤ (divisorSection hI ⊤) m) = 1 := by
  induction m with
  | zero =>
    unfold divisorComplementFunction
    change SectionGradedLocalCoordinates.coordinate _ 0 ⊤ (X.presheaf.map _ 1) = 1
    rw [map_one, SectionGradedLocalCoordinates.coordinate_zero]
  | succ m ih => exact (divisorComplementFunction_cons hI m _).trans ih

/-- The tensorized canonical divisor map acts by prepending the canonical section. -/
theorem divisorTwistedComplex_leftUnitor (m : ℕ)
    (s : Γ(tensorPower (divisorLineBundle I hI) m, ⊤)) :
    (divisorTwistedComplex hI (tensorPower (divisorLineBundle I hI) m)).f.app ⊤
      ((leftUnitor (tensorPower (divisorLineBundle I hI) m)).inv.app ⊤ s) =
        pure _ _ ⊤ (divisorSection hI ⊤) s := by
  change (ModuleSheafTensor.map (divisorSectionMap hI) (𝟙 _)).app ⊤
    ((leftUnitor _).inv.app ⊤ s) = _
  have hu : (leftUnitor (tensorPower (divisorLineBundle I hI) m)).inv.app ⊤ s =
      ModuleSheafTensor.pure (structureModule X) _ ⊤ (1 : Γ(X, ⊤)) s := by
    apply (ConcreteCategory.bijective_of_isIso
      ((leftUnitor (tensorPower (divisorLineBundle I hI) m)).hom.app ⊤)).injective
    exact (congrArg (fun f ↦ f.app ⊤ s) (leftUnitor _).inv_hom_id).trans
      ((leftUnitor_pure _ ⊤ (1 : Γ(X, ⊤)) s).trans (one_smul _ s)).symm
  rw [hu, ModuleSheafTensor.map_pure]
  rfl

end FLT.Mazur.FCurve
