/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelProjectionSections
public import FLT.Mazur.SchemeChartBaseScalars

/-!
# Original base Rees scalars on spectrum charts

The structural base Rees action, restricted through the actual source
preimage, is exactly the original right tensor inclusion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (J : Ideal R)

attribute [local semireducible] modelSpectrum
attribute [local irreducible] chartSpaceMap

/-- The original base Rees scalar on each original source preimage. -/
def modelBaseScalar (V : X.affineOpens) :
    reesAlgebra J →+* Γ(relativeSpace f J, modelSourceProjection f J ⁻¹ᵁ V.1) :=
  ((pullback.snd f (baseMap J)).appLE ⊤ (modelSourceProjection f J ⁻¹ᵁ V.1)
    (by simp)).hom.comp (Scheme.ΓSpecIso (.of (reesAlgebra J))).inv.hom

/-- The base Rees scalar map on original chart sections is the right tensor inclusion. -/
lemma spectrumBaseProjection_appLE (V : X.affineOpens) (a : reesAlgebra J) :
    let _ := chartAlgebra f V
    (spectrumSpaceMap f J V).appLE (modelSourceProjection f J ⁻¹ᵁ V.1) ⊤
        (le_of_eq (spectrumSpaceMap_preimage_source f J V).symm) (modelBaseScalar f J V a) =
      (Scheme.ΓSpecIso (.of (Γ(X, V.1) ⊗[R] reesAlgebra J))).inv
        (Algebra.TensorProduct.includeRight (R := R) (A := Γ(X, V.1)) a) := by
  let _ := chartAlgebra f V
  exact congrArg (fun k ↦ k a) (SchemeChartBaseScalars.chart_appLE
    (.of (reesAlgebra J)) (.of (Γ(X, V.1) ⊗[R] reesAlgebra J))
    (pullback.snd f (baseMap J)) (spectrumSpaceMap f J V)
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
      (R := R) (A := Γ(X, V.1)) (B := reesAlgebra J)).toRingHom)
    (chartSpaceMap_snd f J V) (modelSourceProjection f J ⁻¹ᵁ V.1)
    (spectrumSpaceMap_preimage_source f J V))

end FLT.Mazur.BaseAdicRees
