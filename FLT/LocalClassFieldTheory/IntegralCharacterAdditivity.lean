/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralH2Characters

/-!
# Additivity of the integral character comparison

Pointwise multiplication in the multiplicative notation for characters is
addition of their values, and becomes addition in actual integral cohomology.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

/-- Adding continuous representatives adds their categorical homology classes. -/
theorem cochainHomologyClass_add {k : Type} [CommRing k]
    (K : CochainComplex (ModuleCat k) ℕ) (n : ℕ) (c d : K.X n)
    (hc : (K.d n ((ComplexShape.up ℕ).next n)).hom c = 0)
    (hd : (K.d n ((ComplexShape.up ℕ).next n)).hom d = 0)
    (hcd : (K.d n ((ComplexShape.up ℕ).next n)).hom (c + d) = 0) :
    cochainHomologyClass K n (c + d) hcd =
      cochainHomologyClass K n c hc + cochainHomologyClass K n d hd := by
  unfold cochainHomologyClass
  rw [← map_add]
  apply congrArg (K.homologyπ n).hom
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  simp only [map_add, cochainCyclesMk_val]

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

attribute [local instance] trivialCoefficientAction trivialCoefficientIntComm
  trivialCoefficientContinuous rationalCircleCoefficientTopology rationalCircleCoefficientDiscrete

/-- Adding continuous characters adds their actual H1 classes. -/
theorem integralH1Class_character_mul {A : Type} [AddCommGroup A]
    [TopologicalSpace A] [DiscreteTopology A] (χ ψ : G →ₜ* Multiplicative A) :
    integralH1Class (k := ℤ) (characterCocycle (χ * ψ)) =
      integralH1Class (k := ℤ) (characterCocycle χ) +
        integralH1Class (k := ℤ) (characterCocycle ψ) := by
  unfold integralH1Class
  exact cochainHomologyClass_add (continuousCochains ℤ G A) 1
    (continuousOneCochain (characterCocycle χ).val)
    (continuousOneCochain (characterCocycle ψ).val) _ _ _

/-- The rational-circle description preserves addition in integral H2. -/
theorem integralH2CharacterEquiv_mul (χ ψ : G →ₜ* Multiplicative (AddCircle (1 : ℚ))) :
    integralH2CharacterEquiv G (χ * ψ) =
      integralH2CharacterEquiv G χ + integralH2CharacterEquiv G ψ := by
  rw [integralH2CharacterEquiv_apply, integralH1Class_character_mul, map_add,
    integralH2CharacterEquiv_apply, integralH2CharacterEquiv_apply]

/-- The trivial rational-circle character gives the zero integral H2 class. -/
theorem integralH2CharacterEquiv_one : integralH2CharacterEquiv G 1 = 0 := by
  have h := integralH2CharacterEquiv_mul (G := G) 1 1
  rw [one_mul] at h
  exact add_eq_left.mp h.symm

/-- The zero integral class is precisely the trivial character. -/
theorem integralH2CharacterEquiv_eq_zero (χ : G →ₜ* Multiplicative (AddCircle (1 : ℚ))) :
    integralH2CharacterEquiv G χ = 0 ↔ χ = 1 := by
  rw [← integralH2CharacterEquiv_one (G := G), (integralH2CharacterEquiv G).injective.eq_iff]

end LocalClassFieldTheory
