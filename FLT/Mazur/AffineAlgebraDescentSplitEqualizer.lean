/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineAlgebraDescentCoaction

/-!
# The split equalizer of a multiplicative descent coaction

After tensoring, the coaction itself is an equalizer. The two retractions
are actual multiplication maps, and their identities follow from the given
counit, cocycle and scalar compatibility. No reconstruction is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TensorProduct
namespace FLT.Mazur.AffineAlgebraDescent
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  (D : Data R S B)

/-- Multiplication of the covering scalar and the original coefficient. -/
def multiply : S ⊗[R] B →ₗ[R] B :=
  TensorProduct.lift (Algebra.lsmul R R B (A := S)).toLinearMap

/-- The coaction identifies the original coefficients with a split tensor equalizer. -/
def tensorSplitEqualizer :
    IsSplitEqualizer
      (ModuleCat.ofHom ((D.coaction.toLinearMap.restrictScalars R).lTensor S))
      (ModuleCat.ofHom (AffineTensorCocycle.insertMiddle (1 : S)))
      (ModuleCat.ofHom (D.coaction.toLinearMap.restrictScalars R)) where
  leftRetraction := ModuleCat.ofHom (multiply (R := R) (S := S) (B := B))
  rightRetraction := ModuleCat.ofHom
    (TensorProduct.lift (Algebra.lsmul R R (S ⊗[R] B) (A := S)).toLinearMap)
  condition := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext D.coassoc
  ι_leftRetraction := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext D.counit
  bottom_rightRetraction := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro s b
    change s • ((1 : S) ⊗ₜ[R] b) = s ⊗ₜ[R] b
    rw [smul_tmul', smul_eq_mul, mul_one]
  top_rightRetraction := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro s b
    change s • D.coaction b = D.coaction (s • b)
    exact (map_smul D.coaction s b).symm

/-- The split tensor fork is an actual limiting fork of original base modules. -/
def tensorForkIsLimit : IsLimit (tensorSplitEqualizer D).asFork :=
  (tensorSplitEqualizer D).isEqualizer

end FLT.Mazur.AffineAlgebraDescent
