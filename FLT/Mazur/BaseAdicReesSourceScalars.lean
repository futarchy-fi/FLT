/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelProjectionSections
public import FLT.Mazur.AffineChartSourceScalars

/-!
# Source scalar coordinates of the original Rees chart

The actual source projection induces the original inclusion of the source
chart ring into the tensor ring, with the chosen preimage identification.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (J : Ideal R)

attribute [local semireducible] modelSpectrum
attribute [local irreducible] chartSpaceMap

/-- Original source scalars pull back to their canonical tensor-ring inclusions. -/
lemma spectrumSourceProjection_appLE (V : X.affineOpens) :
    let _ := chartAlgebra f V
    (spectrumSpaceMap f J V ≫ modelSourceProjection f J).appLE V.1 ⊤
        (le_of_eq (spectrumSpaceMap_preimage_source f J V).symm) =
      CommRingCat.ofHom (algebraMap Γ(X, V.1) (Γ(X, V.1) ⊗[R] reesAlgebra J)) ≫
        (Scheme.ΓSpecIso (.of (Γ(X, V.1) ⊗[R] reesAlgebra J))).inv := by
  let _ := chartAlgebra f V
  exact AffineChartSourceScalars.chart_appLE V _ _ _ (chartSpaceMap_fst f J V) _

end FLT.Mazur.BaseAdicRees
