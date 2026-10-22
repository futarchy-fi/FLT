/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalIdealTensorCriterion
public import FLT.Mazur.ResidualPresentationInjectivity

/-!
# The local flatness criterion at a proper ideal

For a finite module over a local Noetherian target, injectivity of the
tensor inclusion for a proper base ideal and flatness of the residual
module imply flatness over the base. The ideal need not be maximal.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.LocalProperIdealTensorCriterion
variable {R S M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [CommRing S] [Algebra R S] [IsNoetherianRing S] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [Module.Finite S M]

include S in
/-- A presentation injective modulo a proper ideal with flat residual cokernel is flat. -/
theorem flat_of_presentation_quotient
    {P N : Type*} [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
    [Module.Flat R N] (f : P →ₗ[R] N) (q : N →ₗ[R] M)
    (he : Function.Exact f q) (hq : Function.Surjective q)
    (I : Ideal R) (hI : I ≠ ⊤) [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)]
    (hf : Function.Injective (f.lTensor (R ⧸ I))) : Module.Flat R M := by
  let a := Ideal.Quotient.factorₐ R (IsLocalRing.le_maximalIdeal hI)
  let _ : Algebra (R ⧸ I) (IsLocalRing.ResidueField R) := a.toRingHom.toAlgebra
  let _ : IsScalarTower R (R ⧸ I) (IsLocalRing.ResidueField R) :=
    IsScalarTower.of_algHom a
  apply LocalIdealTensorCriterion.flat_of_presentation_residue (S := S) f q he hq
  exact ResidualPresentationInjectivity.baseChange_injective
    (R ⧸ I) (IsLocalRing.ResidueField R) f q he hq hf

/-- The proper-ideal tensor test and residual flatness imply flatness of the whole module. -/
theorem flat_of_ideal_injective (I : Ideal R) (hI : I ≠ ⊤)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)]
    (h : Function.Injective (ModuleIdealTensor.inclusion (S := S) (M := M) I)) :
    Module.Flat R M := by
  generalize hqdef : LocalIdealTensorCriterion.presentation (R := R) M = q
  let f : q.ker →ₗ[R] (M →₀ R) := q.ker.subtype
  have hq : Function.Surjective q := by
    rw [← hqdef]
    exact LocalIdealTensorCriterion.presentation_surjective M
  have he : Function.Exact f q := LinearMap.exact_subtype_ker_map q
  have hm : Function.Injective (I.subtype.rTensor M) := by
    apply (I.subtype.lTensor_inj_iff_rTensor_inj M).mp
    intro x y hxy
    apply h
    exact congrArg (AlgebraTensorModule.rid R S M) hxy
  apply flat_of_presentation_quotient (R := R) (S := S)
    (P := q.ker) (N := M →₀ R) f q he hq I hI
  apply IdealTensorPresentationCriterion.quotient_injective
    (R := R) (P := q.ker) (N := M →₀ R) (f := f) (q := q)
    he hq q.ker.subtype_injective I
  exact hm

end FLT.Mazur.LocalProperIdealTensorCriterion
