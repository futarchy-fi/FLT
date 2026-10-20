/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCharacterAdicElements
public import FLT.Mazur.DiagonalizableInfinitesimalIdeal
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# The full initial character kernel lies in the Jacobson radical

Over the original adically complete ring, finiteness of the character group
makes its algebra integral. Maximal ideals therefore contract to maximal
ideals of the base, so all coefficients in the defining ideal vanish there.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteCharacterAdicElements

variable {R G : Type} [CommRing R] [AddCommMonoid G] [Finite G]
  (I : Ideal R) [IsAdicComplete I R]

/-- Every maximal ideal of the original finite character algebra contains the base ideal. -/
theorem scalar_mem_maximal (M : Ideal (AddMonoidAlgebra R G)) [M.IsMaximal]
    {a : R} (ha : a ∈ I) : algebraMap R (AddMonoidAlgebra R G) a ∈ M := by
  let _ : Module.Finite R (AddMonoidAlgebra R G) :=
    Module.Finite.of_basis (AddMonoidAlgebra.basis G R)
  have hm : (M.comap (algebraMap R (AddMonoidAlgebra R G))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
      (Algebra.IsIntegral.isIntegral (R := R) (A := AddMonoidAlgebra R G)) M
  exact (show (⊥ : Ideal R).jacobson ≤ M.comap (algebraMap R _) from
    sInf_le ⟨bot_le, hm⟩) (IsAdicComplete.le_jacobson_bot I ha)

/-- The full original coefficient kernel, not merely its scalar part, is Jacobson. -/
theorem coefficientIdeal_le_jacobson :
    DiagonalizableCobar.coefficientIdeal R G I ≤
      (⊥ : Ideal (AddMonoidAlgebra R G)).jacobson := by
  intro p hp
  apply Ideal.mem_sInf.mpr
  intro M hM
  let _ := hM.2
  have hc := (DiagonalizableCobar.mem_coefficientIdeal R G I p).mp hp
  rw [← p.sum_coeff_single]
  apply Submodule.sum_mem
  intro a _
  have he : AddMonoidAlgebra.single a (p.coeff a) =
      algebraMap R (AddMonoidAlgebra R G) (p.coeff a) *
        AddMonoidAlgebra.single a 1 := by simp
  rw [he]
  exact M.mul_mem_right _ (scalar_mem_maximal I M (hc a))

/-- The actual order-one reduction retains the entire Jacobson kernel. -/
theorem reduction_zero_ker_le_jacobson :
    RingHom.ker (reduction (G := G) I 0) ≤
      (⊥ : Ideal (AddMonoidAlgebra R G)).jacobson := by
  intro p hp
  apply coefficientIdeal_le_jacobson I
  apply (DiagonalizableCobar.mem_coefficientIdeal R G I p).mpr
  intro a
  have hc := congrArg (fun z : AddMonoidAlgebra (R ⧸ I ^ (0 + 1)) G => z.coeff a) hp
  change Ideal.Quotient.mk (I ^ (0 + 1)) (p.coeff a) = 0 at hc
  simpa using Ideal.Quotient.eq_zero_iff_mem.mp hc

end FLT.Mazur.FiniteCharacterAdicElements
