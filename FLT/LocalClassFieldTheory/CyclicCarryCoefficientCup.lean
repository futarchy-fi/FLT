/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CyclicCarryNormSum
public import FLT.LocalClassFieldTheory.TwoExtensionGroupEquivalence

/-!
# Carry evaluation with invariant coefficients

An invariant coefficient sends the positive integral carry to its coefficient
powers. The genuine negative Tate cup keeps the negative sign under this
transport, including at the positive cyclic generator.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {H : Type} [Group H] (M : Rep ℤ H)

/-- Use the representation’s integer-module structure. -/
local instance invariantCoefficientBaseModule : Module ℤ M := M.hV2

/-- Integer multiples of an invariant coefficient form an equivariant scalar map. -/
def invariantScalarCoefficients {G : Type} [Group G] (f : H →* G)
    (x : M.ρ.invariants) : Rep.res f (Rep.trivial ℤ G ℤ) ⟶ M :=
  Rep.ofHom ⟨LinearMap.toSpanSingleton ℤ M x.val, fun g => by
    apply LinearMap.ext_ring
    simpa only [LinearMap.comp_apply, MonoidHom.comp_apply, Representation.trivial_apply,
      LinearMap.toSpanSingleton_apply_one] using (x.property g).symm⟩

variable [Fintype H] (n : ℕ) [NeZero n] (e : H ≃* Multiplicative (ZMod n))

local notation "T" => Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ

/-- The positive carry with coefficients in an invariant element of the representation. -/
def invariantCoefficientCarry (x : M.ρ.invariants) : cocycles₂ M :=
  mapCocycles₂ e.toMonoidHom (invariantScalarCoefficients M e.toMonoidHom x) (cyclicOrdinaryCarry n)

/-- Transport of the positive carry preserves its negative Tate sign. -/
theorem invariantCoefficientCarry_negative_cup (x : M.ρ.invariants) (g : H) :
    tateTwoExtensionMap M (invariantCoefficientCarry M n e x) (-2)
      (tateScalarGenerator ℤ H g) =
    -tateInvariantClass M ((e g).toAdd.val • x) := by
  have h := tateTwoExtensionMap_groupEquivalence T M e
    (invariantScalarCoefficients M e.toMonoidHom x)
    (cyclicOrdinaryCarry n) (tateScalarGenerator ℤ H g)
  rw [tateScalarMap_generator] at h
  have hs := cyclicCarry_negative_cup_sign n (e g).toAdd
  simp only [MulEquiv.coe_toMonoidHom] at h
  simp only [ofAdd_toAdd] at hs
  rw [hs, map_neg, tateZeroGroupEquivalence_class] at h
  refine h.symm.trans ?_
  congr 2
  apply Subtype.ext
  simp only [groupEquivalenceInvariant, invariantScalarCoefficients,
    Submodule.coe_smul_of_tower]
  exact Nat.cast_smul_eq_nsmul ℤ _ _

/-- At the positive cyclic generator, the carry cup is the negative invariant class. -/
theorem invariantCoefficientCarry_positive_generator (hn : 1 < n)
    (x : M.ρ.invariants) (g : H) (hg : e g = Multiplicative.ofAdd 1) :
    tateTwoExtensionMap M (invariantCoefficientCarry M n e x) (-2)
      (tateScalarGenerator ℤ H g) = -tateInvariantClass M x := by
  rw [invariantCoefficientCarry_negative_cup, hg]
  have hval : (1 : ZMod n).val = 1 := ZMod.val_one'' (by omega)
  change -tateInvariantClass M ((1 : ZMod n).val • x) = _
  rw [hval, one_smul]

/-- Negating the positive-generator input removes the negative Tate sign. -/
theorem invariantCoefficientCarry_negative_generator (hn : 1 < n)
    (x : M.ρ.invariants) (g : H) (hg : e g = Multiplicative.ofAdd 1) :
    tateTwoExtensionMap M (invariantCoefficientCarry M n e x) (-2)
      (-tateScalarGenerator ℤ H g) = tateInvariantClass M x := by
  rw [map_neg, invariantCoefficientCarry_positive_generator M n e hn x g hg, neg_neg]

end LocalClassFieldTheory
