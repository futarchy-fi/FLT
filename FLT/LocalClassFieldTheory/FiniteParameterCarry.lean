/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CyclicRootCupBoundary
public import FLT.LocalClassFieldTheory.CyclicCarryCoefficientCup
public import FLT.LocalClassFieldTheory.FiniteContinuousH2Class

/-!
# Finite parameter carries

The continuous carry and the ordinary carry have identical representatives.
Characters on the abelianization are constructed by its universal property.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open groupCohomology

variable {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [NeZero n] (χ : G →* Multiplicative (ZMod n))

/-- Regard a finite-group character as the scalar character used by the carry. -/
def finiteScalarCharacter : ContinuousScalarCharacter G (ZMod n) :=
  ⟨⟨fun g => (χ g).toAdd, continuous_of_discreteTopology⟩,
    fun g h => congrArg Multiplicative.toAdd (map_mul χ g h)⟩

/-- Evaluate a finite character on the additive abelianization. -/
def finiteCharacterAbelianization : Additive (Abelianization G) →+ ZMod n :=
  (Abelianization.lift χ).toAdditiveLeft

omit [TopologicalSpace G] [DiscreteTopology G] [NeZero n] in
/-- The abelianized character has the original value on a group element. -/
theorem finiteCharacterAbelianization_of (g : G) :
    finiteCharacterAbelianization χ (Additive.ofMul (Abelianization.of g)) =
      (χ g).toAdd := rfl

variable (M : Type) [AddCommGroup M] [DistribMulAction G M]

local notation "V" => Rep.of (Representation.ofDistribMulAction ℤ G M)



/-- The ordinary positive parameter carry for any finite character. -/
def finiteParameterCarry (x : (V).ρ.invariants) : cocycles₂ V :=
  mapCocycles₂ χ (invariantScalarCoefficients V χ x) (cyclicOrdinaryCarry n)

variable [IsTopologicalGroup G] [Finite G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M]

/-- The continuous class uses the same scalar carry and invariant coefficient. -/
def finiteParameterCarryClass (x : (V).ρ.invariants) : continuousCohomology ℤ G M 2 :=
  integralH2Class (k := ℤ) (cyclicParameterCarry (finiteScalarCharacter χ) x.val)
    (cyclicParameterCarry_isCocycle _ _ x.property)


/-- Finite comparison preserves the parameter carry, including its sign. -/
theorem finiteParameterCarryClass_ordinary (x : (V).ρ.invariants) :
    (finiteContinuousCohomologyIso ℤ G M 2).hom (finiteParameterCarryClass χ M x) =
      H2π V (finiteParameterCarry χ M x) := by
  rw [finiteParameterCarryClass, finiteContinuousH2Class]
  rfl

end LocalClassFieldTheory
