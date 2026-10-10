/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelBaseScalars
public import FLT.Mazur.BaseAdicReesModelCohomologyFinite
public import FLT.Mazur.IdealPowerScalarLift

/-!
# The named cohomology scalars on the actual direct image

The local base Rees action is the restriction of the scalar map used in
proper coherent finiteness. Its pushforward endomorphism therefore acts on
the original power coordinates by the already constructed coefficient action.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.BaseAdicThickening FLT.Mazur.IdealPowerScalarLift

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{0}} {X : Scheme.{0}} (f : X ⟶ Spec R) (J : Ideal R)

/-- Local model scalars are restrictions of the exact scalar map used for finite cohomology. -/
lemma modelCohomologyScalars_restrict (V : X.affineOpens) (a : reesAlgebra J) :
    (relativeSpace f J).presheaf.map (modelSourceProjection f J ⁻¹ᵁ V.1).leTop.op
        (modelCohomologyScalars f J a) = modelBaseScalar f J V a := rfl

variable [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

/-- The actual pushforward of multiplication by a named global Rees scalar. -/
def modelReesEnd (a : reesAlgebra J) : modelPushforward f J M ⟶ modelPushforward f J M :=
  (pushforward (modelSourceProjection f J)).map
    (scalarEnd (globalModelSheaf f J M) (modelCohomologyScalars f J a))

/-- The global endomorphism restricts to the original local base-scalar action. -/
lemma modelReesEnd_app (V : X.affineOpens) (a : reesAlgebra J)
    (s : Γ(modelPushforward f J M, V.1)) :
    (modelReesEnd f J M a).app V.1 s = modelBaseScalar f J V a •
      (show Γ(globalModelSheaf f J M, modelSourceProjection f J ⁻¹ᵁ V.1) from s) := rfl

attribute [local irreducible] modelPushforwardPowerSectionsIso

/-- Original affine power coordinates retain the exact proper-cohomology scalar action. -/
lemma modelReesEnd_powerSections (V : X.affineOpens) (a : reesAlgebra J)
    (s : Γ(modelPushforward f J M, V.1)) :
    let _ := IdealPowerRees.sectionsModule ((baseIdeal R J).comap f) M V
    (modelPushforwardPowerSectionsIso f J M V).hom ((modelReesEnd f J M a).app V.1 s) =
      chartReesScalars f J V a • (modelPushforwardPowerSectionsIso f J M V).hom s := by
  rw [modelReesEnd_app]
  exact modelPushforwardPowerSectionsIso_base_smul f J M V a s

end FLT.Mazur.BaseAdicRees
