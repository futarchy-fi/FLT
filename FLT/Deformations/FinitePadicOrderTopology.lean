/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.PadicIdealOpen
public import FLT.Deformations.RepresentationTheory.PadicIdealCofinal
public import FLT.Deformations.RepresentationTheory.FlatCofinal

/-!
# The topology of finite free p-adic coefficient orders

A Hausdorff ring topology with continuous p-adic scalar multiplication is
already the module topology. Thus p-power ideals are open and cofinal in the
original topology; no replacement of the representation topology is needed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Deformation
variable (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A]
  [Algebra ℤ_[p] A] [Module.Finite ℤ_[p] A] [Module.Free ℤ_[p] A]
  [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [ContinuousSMul ℤ_[p] A]

/-- Finite freeness forces the given Hausdorff coefficient topology to be the module topology. -/
theorem finitePadicOrder_isModuleTopology : IsModuleTopology ℤ_[p] A := by
  classical
  let b := Module.Free.chooseBasis ℤ_[p] A
  let := Module.Free.ChooseBasisIndex.fintype ℤ_[p] A
  have hc : Continuous b.equivFun.symm := by
    change Continuous (fun x ↦ b.equivFun.symm x)
    simp only [Module.Basis.equivFun_symm_apply]
    fun_prop
  have hi : Continuous b.equivFun := by
    apply (hc.isClosedEmbedding b.equivFun.symm.injective).isEmbedding.continuous_iff.mpr
    simp only [Function.comp_def, LinearEquiv.symm_apply_apply]
    fun_prop
  exact IsModuleTopology.iso
    ({ b.equivFun.symm with continuous_toFun := hc, continuous_invFun := hi } :
      _ ≃L[ℤ_[p]] A)

/-- Every principal p-power ideal is open for the original coefficient topology. -/
theorem finitePadicOrder_p_pow_isOpen (n : ℕ) :
    IsOpen (Ideal.span {(p : A) ^ n} : Set A) := by
  let := finitePadicOrder_isModuleTopology p A
  exact PadicInt.isOpen_span_p_pow p A n

/-- Finite-flatness on p-power reductions is equivalent to the full open-ideal predicate. -/
theorem finitePadicOrder_isFlatAt_iff [IsLocalRing A]
    {K M : Type} [Field K] [NumberField K]
    [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ρ : GaloisRep K A M) :
    ρ.IsFlatAt v ↔ ∀ n : ℕ,
      (ρ.baseChange (A ⧸ Ideal.span {(p : A) ^ n})).HasFlatProlongationAt v :=
  GaloisRep.isFlatAt_iff_of_cofinal_powers v ρ p (finitePadicOrder_p_pow_isOpen p A)
    (PadicInt.exists_p_pow_le_of_isOpen p A)

end Deformation
