/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicGeneratorUnitLift
public import Mathlib.Algebra.Ring.AddAut

/-!
# Full cyclic label automorphisms from units

A unit at the original level permutes every label, including coincident
generator powers. The formula keeps the actual power section and can be
used directly in the common characteristic relabeling group.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.CyclicUnitRelabeling
variable {n : ℕ}

/-- Multiplication by a full-level unit as an automorphism of the cyclic label group. -/
def labelAut (u : (ZMod n)ˣ) : MulAut (Multiplicative (ZMod n)) :=
  AddEquiv.toMultiplicative (AddAut.mulLeft u).toAdd

/-- The label automorphism retains multiplication by the specified original unit. -/
theorem labelAut_apply (u : (ZMod n)ˣ) (i : Multiplicative (ZMod n)) :
    (labelAut u i).toAdd = u.val * i.toAdd := rfl

/-- Relabeling all powers is exactly replacing the original generator by its unit power. -/
theorem relabeled_power {G : Type*} [Group G] (x : G) (hx : x ^ n = 1)
    (u : (ZMod n)ˣ) (i : Multiplicative (ZMod n)) :
    x ^ (labelAut u i).toAdd.val = (x ^ u.val.val) ^ i.toAdd.val := by
  rw [labelAut_apply, ZMod.val_mul, ← pow_mul]
  exact (pow_eq_pow_mod _ hx).symm

variable [NeZero n]

/-- Equal cyclic subgroups admit one actual label automorphism comparing every power. -/
theorem exists_labelAut {G : Type*} [Group G] {x y : G} (hx : x ^ n = 1)
    (h : Subgroup.zpowers x = Subgroup.zpowers y) :
    ∃ e : MulAut (Multiplicative (ZMod n)),
      ∀ i, x ^ (e i).toAdd.val = y ^ i.toAdd.val := by
  obtain ⟨u, hu⟩ := CyclicGeneratorUnitLift.exists_unit_of_zpowers_eq hx h
  exact ⟨labelAut u, fun i ↦ (relabeled_power x hx u i).trans (congrArg (· ^ i.toAdd.val) hu)⟩

end FLT.Mazur.CyclicUnitRelabeling
