/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertLocalizationIsomorphismOpen
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Module

/-!
# Localized basis tuples as actual module isomorphisms

The map from the free coordinate module to the family is an isomorphism
exactly when its prescribed vectors form a basis, in any model of localization.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N] {d : ℕ}

/-- Mapping a basis gives a basis precisely when the linear map is an isomorphism. -/
theorem exists_mapped_basis_iff (b : Module.Basis (Fin d) R M) (f : M →ₗ[R] N) :
    (∃ c : Module.Basis (Fin d) R N, ∀ i, c i = f (b i)) ↔ Function.Bijective f := by
  constructor
  · rintro ⟨c, hc⟩
    have he : (b.equiv c (Equiv.refl _)).toLinearMap = f := by
      apply b.ext
      intro i
      simpa only [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply] using hc i
    rw [← he]
    exact (b.equiv c (Equiv.refl _)).bijective
  · intro hf
    exact ⟨b.map (LinearEquiv.ofBijective f hf), fun _ ↦ rfl⟩

/-- The linear map with the proposed tuple as its columns. -/
def tupleLinearMap (y : Fin d → M) : (Fin d → R) →ₗ[R] M :=
  (Pi.basisFun R (Fin d)).constr R y

variable (S : Submonoid R) (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ]
variable [IsLocalization S Rₛ]
variable {Mₛ : Type*} [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ]
variable [IsScalarTower R Rₛ Mₛ] (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f]

attribute [local instance] LocalizedModule.moduleOfIsLocalization in
/-- The criterion works in every actual localization, not only the quotient implementation. -/
theorem localized_tuple_basis_iff (y : Fin d → M) :
    (∃ c : Module.Basis (Fin d) Rₛ Mₛ, ∀ i, c i = f (y i)) ↔
      Function.Bijective (LocalizedModule.map S (tupleLinearMap y)) := by
  let F := LocalizedModule.mkLinearMap S (Fin d → R)
  let g := IsLocalizedModule.map S F f (tupleLinearMap y)
  let b' := (Pi.basisFun R (Fin d)).ofIsLocalizedModule Rₛ S F
  let g' := g.extendScalarsOfIsLocalization S Rₛ
  have hg : ∀ i, g' (b' i) = f (y i) := by
    intro i
    rw [show b' i = F ((Pi.basisFun R (Fin d)) i) from
      Module.Basis.ofIsLocalizedModule_apply _ _ _ _ i]
    change g (F ((Pi.basisFun R (Fin d)) i)) = _
    rw [IsLocalizedModule.map_apply, tupleLinearMap, Module.Basis.constr_basis]
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective F f]
  change _ ↔ Function.Bijective g'
  rw [← exists_mapped_basis_iff b' g']
  simp only [hg]

end FLT.Mazur.HilbertChart
