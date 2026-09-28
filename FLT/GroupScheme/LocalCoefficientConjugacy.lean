/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalEisensteinPresentation
public import Mathlib.RingTheory.LocalRing.Etale
public import Mathlib.FieldTheory.Normal.Basic

/-!
# Conjugacy of coefficient-ring embeddings

Embeddings of a finite monogenic coefficient ring into the integers of a
normal local extension differ by an integral automorphism. This permits
an arbitrary field isomorphism to be adjusted to respect the coefficient ring.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ThreeAdicPlan

variable (L : Type) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]

/-- A finite unramified coefficient DVR has an integral power basis. -/
theorem existsThreeAdicCoefficientPowerBasis (C : Type) [CommRing C] [IsDomain C]
    [IsDiscreteValuationRing C] [Algebra ℤ_[3] C] [Module.Finite ℤ_[3] C]
    [FaithfulSMul ℤ_[3] C] [Algebra.FormallyUnramified ℤ_[3] C] :
    Nonempty (PowerBasis ℤ_[3] C) := by
  obtain ⟨c, hc⟩ := IsLocalRing.exists_adjoin_eq_top (R := ℤ_[3]) (S := C)
  exact ⟨(IsAdjoinRootMonic.mkOfAdjoinEqTop' hc).powerBasis⟩

/-- Two injective coefficient-ring embeddings into a normal local integer ring
are conjugate under an integral automorphism. -/
theorem threeAdicCoefficientEmbeddingsConjugate [IsGalois ℚ_[3] L]
    {C : Type} [CommRing C] [Algebra ℤ_[3] C] (pc : PowerBasis ℤ_[3] C)
    (f g : C →ₐ[ℤ_[3]] ThreeAdicIntegers L)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ σ : ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L,
      σ.toAlgHom.comp f = g := by
  let i := IsScalarTower.toAlgHom ℤ_[3] (ThreeAdicIntegers L) L
  have hi : Function.Injective i := IsFractionRing.injective _ _
  have hmin : minpoly ℚ_[3] (i (g pc.gen)) = minpoly ℚ_[3] (i (f pc.gen)) := by
    change minpoly ℚ_[3] ((i.comp g) pc.gen) = minpoly ℚ_[3] ((i.comp f) pc.gen)
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[3]
      (pc.isIntegral_gen.map (i.comp g)),
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[3]
      (pc.isIntegral_gen.map (i.comp f))]
    rw [minpoly.algHom_eq (i.comp g) (hi.comp hg),
      minpoly.algHom_eq (i.comp f) (hi.comp hf)]
  obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit L).mp hmin
  let σ := galRestrict ℤ_[3] ℚ_[3] L (ThreeAdicIntegers L) τ
  refine ⟨σ, pc.algHom_ext ?_⟩
  apply hi
  simpa [σ, i, galRestrict, AlgEquiv.smul_def] using hτ

end ThreeAdicPlan
