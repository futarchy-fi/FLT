/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteTowerInflatedCup
public import FLT.LocalClassFieldTheory.TwoExtensionGroupEquivalence
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Quotient-group coefficients in a finite field tower

Restriction identifies the quotient by its kernel with the smaller Galois
group. Inclusion identifies smaller-field units with the kernel invariants.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable (K E L : Type) [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
  [IsGalois K E] [IsGalois K L] [FiniteDimensional K E] [FiniteDimensional K L]

local notation "ME" => Rep.ofAlgebraAutOnUnits K E
local notation "ML" => Rep.ofAlgebraAutOnUnits K L
local notation "f" => (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))
local notation "N" => MonoidHom.ker f
local notation "MQ" => Rep.quotientToInvariants ML N
local notation "φ" => finiteTowerCoefficients K E L

/-- Restriction realizes the quotient Galois group as the smaller-field group. -/
def finiteTowerQuotientGroup : (Gal(L/K) ⧸ N) ≃* Gal(E/K) :=
  QuotientGroup.quotientKerEquivOfSurjective f (AlgEquiv.restrictNormalHom_surjective L)

omit [FiniteDimensional K E] [FiniteDimensional K L] in
/-- The quotient equivalence evaluates a representative by restriction. -/
theorem finiteTowerQuotientGroup_mk (g : Gal(L/K)) :
    finiteTowerQuotientGroup K E L (QuotientGroup.mk' N g) = f g := rfl

omit [IsGalois K L] [FiniteDimensional K E] [FiniteDimensional K L] in
/-- The included smaller-field unit is fixed by the restriction kernel. -/
theorem finiteTowerCoefficients_kernel_fixed (u : Additive Eˣ) (n : N) :
    (ML).ρ (n : Gal(L/K)) ((φ).hom u) = (φ).hom u := by
  rw [← Rep.hom_comm_apply]
  change (φ).hom ((ME).ρ (f n) u) = _
  rw [n.property, map_one, Module.End.one_apply]

/-- The equivariant inclusion into the actual quotient invariant representation. -/
def finiteTowerQuotientCoefficients :
    Rep.res (finiteTowerQuotientGroup K E L).toMonoidHom ME ⟶ MQ :=
  Rep.ofHom ⟨(φ).hom.toLinearMap.codRestrict _ (finiteTowerCoefficients_kernel_fixed K E L),
    fun a => by
      apply LinearMap.ext
      intro u
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N a
      apply Subtype.ext
      exact Rep.hom_comm_apply φ g u⟩

omit [FiniteDimensional K E] [FiniteDimensional K L] in
/-- The kernel-invariant coefficient inclusion is injective. -/
theorem finiteTowerQuotientCoefficients_injective :
    Function.Injective (finiteTowerQuotientCoefficients K E L).hom := by
  intro u v h
  apply Additive.toMul.injective
  apply Units.ext
  apply (algebraMap E L).injective
  exact congrArg (fun x : MQ => ((Additive.toMul x.val : Lˣ) : L)) h

omit [FiniteDimensional K E] in
/-- Every kernel-invariant unit lies in the smaller field. -/
theorem finiteTowerQuotientCoefficients_surjective :
    Function.Surjective (finiteTowerQuotientCoefficients K E L).hom := by
  intro u
  let A := (IsScalarTower.toAlgHom K E L).fieldRange
  have hu : ((Additive.toMul u.val : Lˣ) : L) ∈ A := by
    rw [← IsGalois.fixedField_fixingSubgroup A, IntermediateField.mem_fixedField_iff]
    intro g hg
    have hn : g ∈ N := by
      rw [AlgEquiv.ker_restrictNormalHom]
      exact hg
    exact congrArg (fun x : Additive Lˣ => ((Additive.toMul x : Lˣ) : L))
      (u.property ⟨g, hn⟩)
  obtain ⟨v, hv⟩ := hu
  have hv0 : v ≠ 0 := by
    intro h
    have hz : ((Additive.toMul u.val : Lˣ) : L) = 0 := by
      rw [← hv, h, map_zero]
    exact (Additive.toMul u.val).ne_zero hz
  refine ⟨Additive.ofMul (Units.mk0 v hv0), ?_⟩
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Units.ext
  exact hv

end LocalClassFieldTheory
