/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CyclicRootCupBoundary
public import FLT.LocalClassFieldTheory.DiscreteFieldUnits
public import FLT.GroupScheme.AlgebraicClosureKummer
public import FLT.GroupScheme.RootModuleLinear
public import FLT.GroupScheme.KummerUnitTransport

/-!
# The actual Kummer root cup and its parameter carry

Algebraic closedness supplies the root. Inclusion of the existing continuous
Kummer cup into field units has the negative parameter-carry class.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open groupCohomology GaloisRepresentation.Extensions KummerTheory

variable (K C : Type) [Field K] [Field C] [Algebra K C] [IsGalois K C]
  [IsAlgClosed C] [TopologicalSpace (Additive Cˣ)] [DiscreteTopology (Additive Cˣ)]
  (p : ℕ) [Fact p.Prime]

attribute [local instance] fieldUnitAction

/-- A root of the actual Kummer parameter, obtained from algebraic closedness. -/
def kummerCarryRoot (a : Kˣ) : Cˣ := (exists_unit_root (L := C) (n := p) a).choose

omit [IsGalois K C] [TopologicalSpace (Additive Cˣ)] [DiscreteTopology (Additive Cˣ)] in
/-- The chosen root has the required power, without a root-existence premise. -/
theorem kummerCarryRoot_pow (a : Kˣ) :
    kummerCarryRoot K C p a ^ p = Units.map (RingHom.toMonoidHom (algebraMap K C)) a :=
  (exists_unit_root (L := C) (n := p) a).choose_spec

variable (a : Kˣ) (χ : ContinuousAddCharacter Gal(C/K) (ZMod p))

local notation "b" => Additive.ofMul (kummerCarryRoot K C p a)
local notation "u" => Additive.ofMul (Units.map (RingHom.toMonoidHom (algebraMap K C)) a)

omit [IsGalois K C] [IsAlgClosed C]
  [TopologicalSpace (Additive Cˣ)] [DiscreteTopology (Additive Cˣ)] in
/-- The parameter is fixed by the actual Galois action. -/
theorem kummerCarryParameter_fixed (g : Gal(C/K)) : g • u = u := by
  apply Additive.toMul.injective
  apply Units.ext
  exact g.commutes (a : K)

/-- Inclusion of the existing root-ratio-first cup has its explicit exponent formula. -/
theorem kummerCarryCup_apply (g h : Gal(C/K)) :
    Additive.ofMul (rootUnit
      (continuousCup (continuousRootCocycle a (kummerCarryRoot K C p a)
        (kummerCarryRoot_pow K C p a)) χ (g, h))) =
      cyclicRootRatioCup χ b (g, h) := by
  change Additive.ofMul (rootUnit (χ.val h • _)) = _
  rw [← ZMod.natCast_zmod_val (χ.val h), Nat.cast_smul_eq_nsmul, rootUnit_nsmul]
  rfl

/-- The existing Kummer cup included pointwise into field-unit coefficients. -/
def kummerIncludedCup : C(Gal(C/K) × Gal(C/K), Additive Cˣ) :=
  ⟨fun z => Additive.ofMul (rootUnit
    (continuousCup (continuousRootCocycle a (kummerCarryRoot K C p a)
      (kummerCarryRoot_pow K C p a)) χ z)),
    (continuous_of_discreteTopology (f := fun z : RootModule C p =>
      Additive.ofMul (rootUnit z))).comp (continuousCup
      (continuousRootCocycle a (kummerCarryRoot K C p a)
        (kummerCarryRoot_pow K C p a)) χ).continuous⟩

/-- Inclusion of the existing cup is exactly the root-ratio cup. -/
theorem kummerIncludedCup_eq :
    kummerIncludedCup K C p a χ = cyclicRootRatioCup χ b := by
  apply ContinuousMap.ext
  intro z
  exact kummerCarryCup_apply K C p a χ z.1 z.2

/-- The included Kummer cup is an actual field-unit two-cocycle. -/
theorem kummerIncludedCup_isCocycle : IsCocycle₂ (kummerIncludedCup K C p a χ) := by
  rw [kummerIncludedCup_eq]
  exact cyclicRootRatioCup_isCocycle χ b u
    (congrArg Additive.ofMul (kummerCarryRoot_pow K C p a))
    (kummerCarryParameter_fixed K C a)

/-- The Kummer cup included in field units has the negative positive-carry class. -/
theorem kummerCarryCup_class :
    integralH2Class (k := ℤ) (kummerIncludedCup K C p a χ)
        (kummerIncludedCup_isCocycle K C p a χ) =
      -integralH2Class (k := ℤ) (cyclicParameterCarry χ u)
        (cyclicParameterCarry_isCocycle χ u (kummerCarryParameter_fixed K C a)) := by
  simp only [kummerIncludedCup_eq]
  exact cyclicRootRatioCup_class χ b u
    (congrArg Additive.ofMul (kummerCarryRoot_pow K C p a))
    (kummerCarryParameter_fixed K C a)

end LocalClassFieldTheory
