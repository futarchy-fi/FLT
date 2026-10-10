/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineChartResidueEquation
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The actual cartesian square of an affine residue tensor chart

The tensor spectrum used in section coordinates is the geometric base change
of the original affine morphism. Both structural maps retain the canonical
spectrum isomorphisms, so this square can be pasted into a global family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.AffineSectionTensorSquare
open AffineChartResidueEquation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{0}} [IsAffine X] [IsAffine S]

/-- Tensor coordinates construct the actual affine base-change square. -/
theorem isPullback (f : X ⟶ S) (C : Type) [CommRing C] [Algebra Γ(S, ⊤) C] :
    let _ := f.appTop.hom.toAlgebra
    IsPullback (chartMap (X := X) (Algebra.TensorProduct.includeRight :
      Γ(X, ⊤) →ₐ[Γ(S, ⊤)] C ⊗[Γ(S, ⊤)] Γ(X, ⊤)).toRingHom)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        C →+* C ⊗[Γ(S, ⊤)] Γ(X, ⊤)))) f
      (chartMap (X := S) (algebraMap Γ(S, ⊤) C)) := by
  let _ := f.appTop.hom.toAlgebra
  have h := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(S, ⊤) C Γ(X, ⊤)).flip
  refine h.of_iso (Iso.refl _) X.isoSpec.symm (Iso.refl _) S.isoSpec.symm
    (by simp [chartMap]) (by simp) ?_ (by simp [chartMap])
  exact Scheme.isoSpec_inv_naturality f

end FLT.Mazur.AffineSectionTensorSquare
