/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineAlgebraDescentSplitEqualizer

/-!
# Effective reconstruction of the descended affine algebra

Flatness preserves the fixed-coefficient equalizer. Comparing it with the
split tensor equalizer proves that multiplication reconstructs the original
algebra. The resulting isomorphism is multiplicative and has a specified
formula, so it can be applied to spectra and original descent morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory TensorProduct
namespace FLT.Mazur.AffineAlgebraDescent
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  (D : Data R S B)

/-- The reconstruction is multiplication after inclusion of the fixed coefficients. -/
def reconstruct : S ⊗[R] invariants D →ₐ[S] B :=
  AlgHom.liftEquiv R S (invariants D) B (invariants D).val

/-- The original multiplication formula on every pure tensor. -/
theorem reconstruct_tmul (s : S) (b : invariants D) :
    reconstruct D (s ⊗ₜ[R] b) = s • b.val := rfl

/-- The reconstruction retains the specified coaction on the whole tensor algebra. -/
theorem reconstruct_coaction (t : S ⊗[R] invariants D) :
    D.coaction (reconstruct D t) = (inclusion D).hom.lTensor S t := by
  induction t using TensorProduct.inductionOn with
  | tmul s b =>
    rw [reconstruct_tmul, map_smul, (mem_invariants D b.val).mp b.property]
    change s • ((1 : S) ⊗ₜ[R] b.val) = s ⊗ₜ[R] b.val
    rw [smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The tensor of the original invariant fork, written with its actual coefficient maps. -/
def tensorInvariantFork : Fork
    (ModuleCat.ofHom ((D.coaction.toLinearMap.restrictScalars R).lTensor S))
    (ModuleCat.ofHom (AffineTensorCocycle.insertMiddle (1 : S))) :=
  Fork.ofι (ModuleCat.ofHom ((inclusion D).hom.lTensor S)) (by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro s b
    change s ⊗ₜ[R] D.coaction b.val = s ⊗ₜ[R] ((1 : S) ⊗ₜ[R] b.val)
    rw [(mem_invariants D b.val).mp b.property])

variable [Module.Flat R S]

/-- Flatness proves that the tensor invariant fork is a limit. -/
def tensorInvariantForkIsLimit : IsLimit (tensorInvariantFork D) := by
  let F := tensorLeft (ModuleCat.of R S)
  have h := isLimitForkMapOfIsLimit F (invariantFork D).condition
    (invariantForkIsLimit D)
  exact h

/-- The two independently proved equalizers identify their coefficient modules. -/
def coefficientIso : ModuleCat.of R (S ⊗[R] invariants D) ≅ ModuleCat.of R B :=
  (tensorInvariantForkIsLimit D).conePointUniqueUpToIso (tensorForkIsLimit D)

/-- The equalizer comparison is exactly the original algebra reconstruction map. -/
theorem coefficientIso_hom :
    (coefficientIso D).hom = ModuleCat.ofHom ((reconstruct D).toLinearMap.restrictScalars R) := by
  apply Fork.IsLimit.hom_ext (tensorForkIsLimit D)
  have h := (tensorInvariantForkIsLimit D).conePointUniqueUpToIso_hom_comp
    (tensorForkIsLimit D) WalkingParallelPair.zero
  exact h.trans (ModuleCat.hom_ext
    (LinearMap.ext (fun t ↦ (reconstruct_coaction D t).symm)))

/-- Scalar extension of the constructed coordinate ring is the entire original algebra. -/
theorem reconstruct_bijective : Function.Bijective (reconstruct D) := by
  have h := (ConcreteCategory.isIso_iff_bijective (coefficientIso D).hom).mp inferInstance
  rwa [coefficientIso_hom] at h

/-- Effective affine algebra descent with a multiplicative reconstruction isomorphism. -/
def reconstruction : S ⊗[R] invariants D ≃ₐ[S] B :=
  AlgEquiv.ofBijective (reconstruct D) (reconstruct_bijective D)

end FLT.Mazur.AffineAlgebraDescent
