/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.NormalFixedFieldNorm

/-!
# Fixed-field units as subgroup invariants

Both a fixed unit and its inverse lie in the fixed field. This gives the
actual equivalence, with the previously constructed inclusion as forward map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (H : Subgroup Gal(L/K))

local notation "E" => IntermediateField.fixedField H
local notation "MH" => Rep.res H.subtype (Rep.ofAlgebraAutOnUnits K L)

/-- Inclusion of fixed-field units is injective. -/
theorem fixedUnitInvariantInclusion_injective :
    Function.Injective (fixedUnitInvariantInclusion K L H) := by
  intro u v h
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  exact congrArg (fun x : (MH).ρ.invariants => ((Additive.toMul (x.val : Additive Lˣ) : Lˣ) : L)) h

/-- Every subgroup-invariant unit descends to the fixed field. -/
theorem fixedUnitInvariantInclusion_surjective :
    Function.Surjective (fixedUnitInvariantInclusion K L H) := by
  intro u
  have hx : ((Additive.toMul (u.val : Additive Lˣ) : Lˣ) : L) ∈ E := by
    intro g
    exact congrArg (fun x : Additive Lˣ => ((Additive.toMul x : Lˣ) : L)) (u.property g)
  let x : E := ⟨(Additive.toMul (u.val : Additive Lˣ) : Lˣ), hx⟩
  have hn : x ≠ 0 := fun h =>
    (Additive.toMul (u.val : Additive Lˣ)).ne_zero (congrArg Subtype.val h)
  refine ⟨Additive.ofMul (Units.mk0 x hn), ?_⟩
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Units.ext
  rfl

/-- The fixed-field unit equivalence with the actual subgroup invariant module. -/
def fixedUnitInvariantEquiv : Additive Eˣ ≃ₗ[ℤ] (MH).ρ.invariants :=
  LinearEquiv.ofBijective (fixedUnitInvariantInclusion K L H)
    ⟨fixedUnitInvariantInclusion_injective K L H, fixedUnitInvariantInclusion_surjective K L H⟩

end LocalClassFieldTheory
