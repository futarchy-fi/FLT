/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBasisSumCoproduct
public import FLT.Mazur.BaseAdicReesModelPowerNaturality
public import FLT.Mazur.BaseAdicReesModelSourceScalars

/-!
# The actual affine direct image is the sheaf sum of the original powers

The original affine coordinates assemble by their proved naturality and
source linearity. The target is the categorical sum in module sheaves;
no assertion about pointwise sums on arbitrary opens is needed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] modelPushforward modelPushforwardPowerSectionsIso

/-- The original powers of the pulled-back base ideal, as actual module sheaves. -/
abbrev modelPowerSheaves (n : ℕ) : X.Modules :=
  GlobalIdealPower.multiple (((baseIdeal R J).comap f) ^ n) M

/-- The actual direct-image coordinates form an isomorphism on the affine basis. -/
def modelPowerBasisIso :
    AffineBasisModuleMorphism.basis (modelPushforward f J M) ≅
      AffineBasisDirectSum.sum (modelPowerSheaves f J M) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun U ↦ modelPushforwardPowerSectionsIso f J M U.unop) (by
      intro U V i
      apply ConcreteCategory.hom_ext
      intro s
      exact modelPushforwardPowerSectionsIso_naturality f J M i.unop.le s))

/-- Each original ideal power maps into the actual global affine direct image. -/
def modelPowerInclusion (n : ℕ) : modelPowerSheaves f J M n ⟶ modelPushforward f J M :=
  AffineBasisSumMaps.ι _ _ (modelPowerBasisIso f J M)
    (modelPushforwardPowerSectionsIso_smul f J M) n

/-- The actual affine direct image is the coproduct of the original ideal-power sheaves. -/
def modelPowerCofanIsColimit :
    IsColimit (Cofan.mk (modelPushforward f J M) (modelPowerInclusion f J M)) :=
  AffineBasisSumMaps.isColimit _ _ (modelPowerBasisIso f J M)
    (modelPushforwardPowerSectionsIso_smul f J M)

/-- The global direct-image/sheaf-sum identification for the fixed proper model. -/
def modelPushforwardSheafSumIso : modelPushforward f J M ≅ ∐ (modelPowerSheaves f J M) :=
  AffineBasisSumMaps.coproductIso _ _ (modelPowerBasisIso f J M)
    (modelPushforwardPowerSectionsIso_smul f J M)

/-- The comparison preserves the original degree inclusions. -/
lemma modelPowerInclusion_sheafSumIso (n : ℕ) :
    modelPowerInclusion f J M n ≫ (modelPushforwardSheafSumIso f J M).hom =
      Sigma.ι (modelPowerSheaves f J M) n :=
  AffineBasisSumMaps.ι_coproductIso_hom _ _ (modelPowerBasisIso f J M)
    (modelPushforwardPowerSectionsIso_smul f J M) n

end FLT.Mazur.BaseAdicRees
