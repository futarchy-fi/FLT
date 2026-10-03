/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.LinearClassCoordinates
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The canonical tensor comparison for continuous character classes

A finite coefficient basis constructs the comparison. Its pure-tensor
formula identifies it with scalar multiplication after coefficient inclusion,
and proves that the resulting map does not depend on that basis.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

open TensorProduct

variable {F k G ι : Type*} [Field F] [Field k] [Algebra F k]
    [Group G] [TopologicalSpace G] [Fintype ι]
    (χ : G →* Fˣ) (b : Module.Basis ι F k)

/-- The scalar-extension inclusion as a semilinear coefficient map. -/
def characterInclusionSemilinear : CharacterModule χ F →ₛₗ[algebraMap F k] CharacterModule χ k where
  toFun x := algebraMap F k x
  map_add' x y := map_add (algebraMap F k) x y
  map_smul' a x := map_mul (algebraMap F k) a x

/-- The canonical inclusion on continuous classes. -/
noncomputable def extendCharacterClass : LinearContinuousClass F G (CharacterModule χ F) →ₛₗ[
    algebraMap F k] LinearContinuousClass k G (CharacterModule χ k) :=
  linearCoefficientClass (characterInclusionSemilinear (k := k) χ)
    (characterCoefficientInclusion_equivariant χ k)

omit [TopologicalSpace G] [Fintype ι] in
/-- Basis coordinates of multiplication by an element of the smaller field. -/
theorem characterBasis_mul (a : k) (z : F) (i : ι) :
    b.repr (a * algebraMap F k z) i = b.repr a i * z := by
  rw [mul_comm, ← Algebra.smul_def, map_smul]
  change z * b.repr a i = b.repr a i * z
  exact mul_comm _ _

/-- Coordinates of a scalar multiple of an included class are the expected scalar multiples. -/
theorem coordinate_smul_extend (a : k) (x : LinearContinuousClass F G (CharacterModule χ F))
    (i : ι) :
    linearCharacterCoordinates χ b (a • extendCharacterClass (k := k) χ x) i = b.repr a i • x := by
  induction x using Quotient.inductionOn with | h c =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    exact characterBasis_mul b a (c.1 g) i

/-- Tensoring prime-character classes gives all continuous extended-character classes. -/
noncomputable def tensorCharacterClassEquiv :
    k ⊗[F] LinearContinuousClass F G (CharacterModule χ F) ≃ₗ[F]
      LinearContinuousClass F G (CharacterModule χ k) := by
  classical
  exact (TensorProduct.equivFinsuppOfBasisLeft b).trans
    ((Finsupp.linearEquivFunOnFinite F _ ι).trans (linearCharacterCoordinatesEquiv χ b).symm)

/-- Pure tensors map to scalar multiples of the actual coefficient inclusion. -/
theorem tensorCharacterClassEquiv_tmul (a : k)
    (x : LinearContinuousClass F G (CharacterModule χ F)) :
    tensorCharacterClassEquiv χ b (a ⊗ₜ[F] x) = a • extendCharacterClass (k := k) χ x := by
  classical
  apply (linearCharacterCoordinatesEquiv χ b).injective
  simp only [tensorCharacterClassEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  funext i
  exact (TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply b a x i).trans
    (coordinate_smul_extend χ b a x i).symm

/-- Regard the target quotient with its extended-field scalar structure. -/
noncomputable def tensorCharacterClassAddEquiv :
    k ⊗[F] LinearContinuousClass F G (CharacterModule χ F) ≃+
      LinearContinuousClass k G (CharacterModule χ k) :=
  (tensorCharacterClassEquiv χ b).toAddEquiv.trans (AddEquiv.refl _)

/-- The pure-tensor formula in the extended-field target. -/
theorem tensorCharacterClassAddEquiv_tmul (a : k)
    (x : LinearContinuousClass F G (CharacterModule χ F)) :
    tensorCharacterClassAddEquiv χ b (a ⊗ₜ[F] x) = a • extendCharacterClass (k := k) χ x :=
  tensorCharacterClassEquiv_tmul χ b a x

/-- The canonical comparison commutes with scalars in the extended field. -/
theorem tensorCharacterClassEquiv_smul (a : k)
    (z : k ⊗[F] LinearContinuousClass F G (CharacterModule χ F)) :
    tensorCharacterClassAddEquiv χ b (a • z) = a • tensorCharacterClassAddEquiv χ b z := by
  induction z using TensorProduct.inductionOn with
  | tmul r x =>
    rw [TensorProduct.smul_tmul', tensorCharacterClassAddEquiv_tmul,
      tensorCharacterClassAddEquiv_tmul, smul_smul]
    rfl
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- The scalar-extension comparison is an equivalence over the extended field itself. -/
noncomputable def tensorCharacterClassLinearEquiv :
    k ⊗[F] LinearContinuousClass F G (CharacterModule χ F) ≃ₗ[k]
      LinearContinuousClass k G (CharacterModule χ k) :=
  { tensorCharacterClassAddEquiv χ b with
    map_smul' := tensorCharacterClassEquiv_smul χ b }

/-- The scalar-extension comparison is independent of the auxiliary finite coefficient basis. -/
theorem tensorCharacterClassEquiv_basis_independent {κ : Type*} [Fintype κ]
    (d : Module.Basis κ F k) :
    (tensorCharacterClassEquiv χ b).toLinearMap = (tensorCharacterClassEquiv χ d).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    exact (tensorCharacterClassEquiv_tmul χ b a x).trans
      (tensorCharacterClassEquiv_tmul χ d a x).symm
  | add x y hx hy => simp only [map_add, hx, hy]

end GaloisRepresentation.Extensions
