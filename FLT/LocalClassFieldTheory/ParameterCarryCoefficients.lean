/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ScalarCarryCharacter
public import FLT.LocalClassFieldTheory.ContinuousColimitNaturality

/-!
# Coefficient maps of parameter carries

The actual continuous cohomology coefficient map takes the parameter to its
coefficient image. Integer parameters give integer multiples of the scalar carry.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {G M P : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]
  [AddCommGroup P] [DistribMulAction G P]
  (φ : Rep.of (Representation.ofDistribMulAction ℤ G M) ⟶
    Rep.of (Representation.ofDistribMulAction ℤ G P))
  (a : M) (ha : ∀ g : G, g • a = a)

include ha in
/-- An equivariant coefficient map preserves a fixed parameter. -/
theorem parameterCarryMapped_fixed (g : G) : g • φ.hom a = φ.hom a :=
  (Rep.hom_comm_apply φ g a).symm.trans (congrArg φ.hom (ha g))

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]
  {n : ℕ} [NeZero n] (χ : ContinuousScalarCharacter G (ZMod n))

/-- The categorical coefficient map preserves the actual carry class. -/
theorem parameterCarry_coefficient_class :
    (continuousCoefficientCohomologyMap φ 2).hom
      (integralH2Class (k := ℤ) (cyclicParameterCarry χ a)
        (cyclicParameterCarry_isCocycle χ a ha)) =
    integralH2Class (k := ℤ) (cyclicParameterCarry χ (φ.hom a))
      (cyclicParameterCarry_isCocycle χ (φ.hom a) (parameterCarryMapped_fixed φ a ha)) := by
  have he := continuousInflationH2_class (MonoidHom.id G) continuous_id φ
    (cyclicParameterCarry χ a) (cyclicParameterCarry_isCocycle χ a ha)
  refine he.trans ?_
  congr 1
  apply ContinuousMap.ext
  intro z
  exact map_zsmul φ.hom _ _

attribute [local instance] trivialCoefficientAction trivialCoefficientIntComm
  trivialCoefficientContinuous

/-- Integer coefficients multiply the scalar carry in actual H². -/
theorem parameterCarry_integer_class (m : ℤ) :
    integralH2Class (k := ℤ) (cyclicParameterCarry χ m)
      (cyclicParameterCarry_isCocycle χ m (fun _ => rfl)) = m • scalarCarryClass χ := by
  let c : continuousTwoCocycles (G := G) (M := ℤ) :=
    ⟨cyclicParameterCarry χ 1, cyclicParameterCarry_isCocycle χ 1 (fun _ => rfl)⟩
  change _ = m • integralH2ClassHom c
  rw [← map_zsmul]
  congr 1
  apply ContinuousMap.ext
  intro z
  change cyclicCarry (χ.val z.1) (χ.val z.2) • m =
    m • (cyclicCarry (χ.val z.1) (χ.val z.2) • (1 : ℤ))
  simp [mul_comm]

end LocalClassFieldTheory
