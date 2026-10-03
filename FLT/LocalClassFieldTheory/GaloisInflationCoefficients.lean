/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.GaloisKernelTopology

/-!
# Multiplicative coefficients for Galois inflation

Inclusion of units of an intermediate Galois field identifies those units
with the invariants of the actual restriction kernel.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  (E : IntermediateField K L) [IsGalois K E]

attribute [local instance] fieldUnitAction

local notation "res" => (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))

/-- Inclusion of field units as an equivariant integral coefficient map. -/
def galoisInflationCoefficients :
    Rep.res res (Rep.of (Representation.ofDistribMulAction ℤ Gal(E/K) (Additive Eˣ))) ⟶
      Rep.of (Representation.ofDistribMulAction ℤ Gal(L/K) (Additive Lˣ)) :=
  Rep.ofHom ⟨(Units.map E.val.toMonoidHom).toAdditive.toIntLinearMap,
    fun g => by
      apply LinearMap.ext
      intro u
      apply Additive.toMul.injective
      apply Units.ext
      exact AlgEquiv.restrictNormal_apply E g (Additive.toMul u : Eˣ)⟩

omit [IsGalois K L] in
/-- Inclusion of intermediate field units is injective. -/
theorem galoisInflationCoefficients_injective :
    Function.Injective (galoisInflationCoefficients K L E).hom := by
  intro u v h
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  exact congrArg (fun w : Additive Lˣ => (↑(Additive.toMul w) : L)) h

/-- Every coefficient fixed by the restriction kernel is an intermediate field unit. -/
theorem galoisInflationCoefficients_fixed (p : Additive Lˣ)
    (hp : ∀ n : Gal(L/K), res n = 1 → n • p = p) :
    ∃ m, (galoisInflationCoefficients K L E).hom m = p := by
  have hx : (↑(Additive.toMul p) : L) ∈ E := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro g hg
    have hr : res g = 1 := by
      change g ∈ (res).ker
      rwa [E.restrictNormalHom_ker]
    exact congrArg (fun w : Additive Lˣ => (↑(Additive.toMul w) : L)) (hp g hr)
  let x : E := ⟨↑(Additive.toMul p), hx⟩
  have hn : x ≠ 0 := fun h => (Additive.toMul p).ne_zero (congrArg Subtype.val h)
  refine ⟨Additive.ofMul (Units.mk0 x hn), ?_⟩
  apply Additive.toMul.injective
  exact Units.ext rfl

end LocalClassFieldTheory
