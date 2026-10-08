/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBasisModuleIso
public import FLT.Mazur.BaseAdicReesModelSheafSum
public import FLT.Mazur.NoetherianModuleSum

/-!
# Original power coordinates on every open of a Noetherian source

The actual direct image is identified with the original sectionwise module sum.
This supplies genuine finite-support global coordinates, with the original
structure-sheaf action and the previously chosen affine coordinates.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped DirectSum

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X]
  (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] modelPushforward modelPushforwardPowerSectionsIso

/-- The actual direct image has the original finite-support coordinates on all opens. -/
def modelPointwiseSumIso :
    modelPushforward f J M ≅ NoetherianModuleSum.sum (modelPowerSheaves f J M) :=
  AffineBasisModuleMorphism.extendIso _ _
    (modelPowerBasisIso f J M ≪≫ (NoetherianModuleSum.basisIso _).symm) (by
      intro U r s
      exact modelPushforwardPowerSectionsIso_smul f J M U r s)

/-- On affine opens this is precisely the previously constructed actual coordinate map. -/
lemma modelPointwiseSumIso_hom_app (U : X.affineOpens) :
    (modelPointwiseSumIso f J M).hom.app U.1 =
      (modelPushforwardPowerSectionsIso f J M U).hom :=
  AffineBasisModuleMorphism.extendIso_hom_app _ _ _ _ U

/-- Original section coordinates on every open, linear over that open's actual ring. -/
def modelPowerSectionsEquiv (U : X.Opens) :
    Γ(modelPushforward f J M, U) ≃ₗ[Γ(X, U)] (⨁ n, Γ(modelPowerSheaves f J M n, U)) :=
  ((SheafOfModules.evaluation X.ringCatSheaf (.op U)).mapIso
    (modelPointwiseSumIso f J M)).toLinearEquiv

/-- The section equivalence retains the chosen affine coordinates. -/
lemma modelPowerSectionsEquiv_affine (U : X.affineOpens)
    (s : Γ(modelPushforward f J M, U.1)) :
    modelPowerSectionsEquiv f J M U.1 s =
      (modelPushforwardPowerSectionsIso f J M U).hom s :=
  ConcreteCategory.congr_hom (modelPointwiseSumIso_hom_app f J M U) s

/-- Every degree of the global identification restricts by its original power sheaf map. -/
lemma modelPowerSectionsEquiv_restrict {U V : X.Opens} (h : U ≤ V)
    (s : Γ(modelPushforward f J M, V)) (n : ℕ) :
    modelPowerSectionsEquiv f J M U
        ((modelPushforward f J M).presheaf.map (homOfLE h).op s) n =
      (modelPowerSheaves f J M n).presheaf.map (homOfLE h).op
        (modelPowerSectionsEquiv f J M V s n) := by
  exact congrArg (fun t : ⨁ n, Γ(modelPowerSheaves f J M n, U) ↦ t n)
    (ConcreteCategory.congr_hom ((modelPointwiseSumIso f J M).hom.mapPresheaf.naturality
      (homOfLE h).op) s)

end FLT.Mazur.BaseAdicRees
