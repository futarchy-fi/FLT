/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousConnectingMap
public import FLT.LocalClassFieldTheory.RationalTorsion

/-!
# The discrete integral-rational coefficient sequence

We equip Z, Q and Q/Z with the trivial group action and discrete topology.
The quotient map has kernel Z, giving an actual continuous connecting map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

/-- The trivial additive action, used explicitly for rational coefficients. -/
@[instance_reducible] def trivialCoefficientAction (G A : Type*) [Group G] [AddCommGroup A] :
    DistribMulAction G A where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

variable (G : Type) [Group G]

attribute [local instance] trivialCoefficientAction
/-- Discrete topology for rational cohomology coefficients. -/
local instance rationalCoefficientTopology : TopologicalSpace ℚ := ⊥
local instance rationalCoefficientDiscrete : DiscreteTopology ℚ := ⟨rfl⟩
/-- Discrete topology for rational-circle cohomology coefficients. -/
local instance rationalCircleCoefficientTopology : TopologicalSpace (AddCircle (1 : ℚ)) := ⊥
local instance rationalCircleCoefficientDiscrete : DiscreteTopology (AddCircle (1 : ℚ)) := ⟨rfl⟩
local instance trivialCoefficientIntComm (A : Type) [AddCommGroup A] :
    SMulCommClass G ℤ A := ⟨fun _ _ _ => rfl⟩
local instance trivialCoefficientContinuous [TopologicalSpace G] (A : Type)
    [AddCommGroup A] [TopologicalSpace A] :
    ContinuousSMul G A :=
  ⟨continuous_snd⟩

/-- Integer inclusion as a morphism of trivial representations. -/
def integralRationalInclusion :
    Rep.of (Representation.ofDistribMulAction ℤ G ℤ) ⟶
      Rep.of (Representation.ofDistribMulAction ℤ G ℚ) :=
  Rep.ofHom ⟨(Int.castAddHom ℚ).toIntLinearMap, fun _ => rfl⟩

/-- The rational quotient as a morphism of trivial representations. -/
def rationalCircleProjection :
    Rep.of (Representation.ofDistribMulAction ℤ G ℚ) ⟶
      Rep.of (Representation.ofDistribMulAction ℤ G (AddCircle (1 : ℚ))) :=
  Rep.ofHom ⟨(QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).toIntLinearMap,
    fun _ => rfl⟩

/-- Integers map to zero in Q/Z. -/
theorem integralRational_comp_projection :
    integralRationalInclusion G ≫ rationalCircleProjection G = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  change ((z : ℚ) : AddCircle (1 : ℚ)) = 0
  apply (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr
  exact ⟨z, by simp⟩

/-- Integer inclusion is injective. -/
theorem integralRationalInclusion_injective :
    Function.Injective (integralRationalInclusion G).hom :=
  Int.cast_injective

/-- Every rational circle class has a rational representative. -/
theorem rationalCircleProjection_surjective :
    Function.Surjective (rationalCircleProjection G).hom :=
  QuotientAddGroup.mk'_surjective _

/-- The kernel of Q to Q/Z is exactly the included integers. -/
theorem rationalCircleProjection_kernel (q : ℚ) :
    (rationalCircleProjection G).hom q = 0 ↔ ∃ z : ℤ, (integralRationalInclusion G).hom z = q := by
  change (q : AddCircle (1 : ℚ)) = 0 ↔ ∃ z : ℤ, (z : ℚ) = q
  simpa using (AddCircle.coe_eq_zero_iff (p := (1 : ℚ)) (x := q))

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The actual short exact sequence of continuous integral coefficient complexes. -/
theorem rationalCoefficientSequence_shortExact :
    (continuousCoefficientShortComplex (integralRationalInclusion G) (rationalCircleProjection G)
      (integralRational_comp_projection G)).ShortExact :=
  continuousCoefficientShortComplex_shortExact _ _ _ (integralRationalInclusion_injective G)
    (rationalCircleProjection_surjective G) (rationalCircleProjection_kernel G)

/-- The Q/Z-to-Z boundary in the actual continuous complex, in every degree. -/
def rationalIntegralConnectingMap (n : ℕ) :
    (continuousCochains ℤ G (AddCircle (1 : ℚ))).homology n ⟶
      (continuousCochains ℤ G ℤ).homology (n + 1) :=
  continuousConnectingMap _ _ (integralRational_comp_projection G)
    (integralRationalInclusion_injective G) (rationalCircleProjection_surjective G)
    (rationalCircleProjection_kernel G) n

end LocalClassFieldTheory
