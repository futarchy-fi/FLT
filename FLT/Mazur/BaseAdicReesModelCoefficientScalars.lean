/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelSectionCoordinates

/-!
# Scalar compatibility of original model coefficients

The canonical global-section coefficient map is linear for the original
tensor-ring action, using the canonical spectrum scalar identification.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

/-- The actual coefficient comparison retains the native tensor-ring scalar action. -/
lemma modelSheafTopCoefficientsEquiv_smul (V : X.affineOpens)
    (a : let _ := chartAlgebra f V; Γ(X, V.1) ⊗[R] reesAlgebra J)
    (s : Γ(modelSheaf f J V M, ⊤)) :
    let _ := chartAlgebra f V
    modelSheafTopCoefficientsEquiv f J M V
        ((Scheme.ΓSpecIso (.of (Γ(X, V.1) ⊗[R] reesAlgebra J))).inv a • s) =
      a • modelSheafTopCoefficientsEquiv f J M V s := by
  let _ := chartAlgebra f V
  exact ((tilde.toTildeΓNatIso (R := .of (Γ(X, V.1) ⊗[R] reesAlgebra J))).app
    (nativeModule f J M V)).symm.toLinearEquiv.map_smul a s

end FLT.Mazur.BaseAdicRees
