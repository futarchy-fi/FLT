/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod

/-!
# Normal p-subgroups in characteristic p

A normal finite p-subgroup acts trivially on an irreducible representation
in characteristic p. The fixed vector argument uses a finite orbit span over
the prime field, so the coefficient field need not be finite.
-/

@[expose] public noncomputable section

namespace Representation

variable {p : ℕ} [Fact p.Prime] {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod p) V]

/-- A p-group acting on a nonzero finite vector space over the prime field
has a nonzero fixed vector. -/
theorem exists_ne_zero_fixed_of_isPGroup [Finite V] [Nontrivial V]
    (ρ : Representation (ZMod p) G V) (hG : IsPGroup p G) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : G, ρ g v = v := by
  let : MulAction G V := {
    smul g v := ρ g v
    one_smul v := by change ρ 1 v = v; simp
    mul_smul g h v := by change ρ (g * h) v = ρ g (ρ h v); simp [Module.End.mul_apply] }
  have hcard : p ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    exact dvd_pow_self p (Module.finrank_pos.ne')
  obtain ⟨v, hv, hv0⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hcard
    (a := 0) (by intro g; exact map_zero (ρ g))
  exact ⟨v, Ne.symm hv0, hv⟩

/-- A finite p-group has a fixed vector on every nonzero prime-field
representation, even when its dimension is infinite. -/
theorem exists_ne_zero_fixed_of_finite_isPGroup [Finite G] [Nontrivial V]
    (ρ : Representation (ZMod p) G V) (hG : IsPGroup p G) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : G, ρ g v = v := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S := Submodule.span (ZMod p) (Set.range fun g : G ↦ ρ g v)
  have hS (g : G) {w : V} (hw : w ∈ S) : ρ g w ∈ S := by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, by simp [Module.End.mul_apply]⟩
    | zero => simp
    | add x y hx hy hx' hy' => simpa using S.add_mem hx' hy'
    | smul a x hx hx' => simpa using S.smul_mem a hx'
  have hvS : v ∈ S := Submodule.subset_span ⟨1, by simp⟩
  have : Nontrivial S := ⟨⟨⟨v, hvS⟩, 0, fun h ↦ hv (congrArg Subtype.val h)⟩⟩
  have : Module.Finite (ZMod p) S := Module.Finite.span_of_finite _ (Set.finite_range _)
  have : Finite S := Module.finite_of_finite (ZMod p)
  let σ : Representation (ZMod p) G S :=
    { toFun := fun g ↦ (ρ g).restrict (fun _ hw ↦ hS g hw)
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp [Module.End.mul_apply] }
  obtain ⟨w, hw, hfix⟩ := σ.exists_ne_zero_fixed_of_isPGroup hG
  exact ⟨w, fun h ↦ hw (Subtype.ext h), fun g ↦ congrArg Subtype.val (hfix g)⟩

section GeneralField

variable {k W : Type*} [Field k] [CharP k p] [AddCommGroup W] [Module k W]

/-- A finite p-group has a nonzero fixed vector over any field of
characteristic p. Only the orbit span over the prime field needs to be finite. -/
theorem exists_ne_zero_fixed_of_charP [Finite G] [Nontrivial W]
    (ρ : Representation k G W) (hG : IsPGroup p G) :
    ∃ w : W, w ≠ 0 ∧ ∀ g : G, ρ g w = w := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  let : Module (ZMod p) W := Module.compHom W (algebraMap (ZMod p) k)
  let : IsScalarTower (ZMod p) k W := IsScalarTower.of_compHom _ _ _
  let σ : Representation (ZMod p) G W :=
    { toFun := fun g ↦ (ρ g).restrictScalars (ZMod p)
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp [Module.End.mul_apply] }
  exact σ.exists_ne_zero_fixed_of_finite_isPGroup hG

/-- A finite normal p-subgroup acts trivially on every irreducible
representation in characteristic p. No dimension hypothesis is needed. -/
theorem normal_pSubgroup_acts_trivially (ρ : Representation k G W)
    [IsIrreducible ρ] (P : Subgroup G) [P.Normal] [Finite P]
    (hP : IsPGroup p P) : ∀ g : P, ∀ w : W, ρ g w = w := by
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra k G) _
  have : Nontrivial W := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨w, hw, hfix⟩ := exists_ne_zero_fixed_of_charP (ρ.comp P.subtype) hP
  let S : Subrepresentation ρ :=
    { toSubmodule := invariants (ρ.comp P.subtype)
      apply_mem_toSubmodule := fun g _ hx ↦ ρ.le_comap_invariants P g hx }
  have hS : S ≠ ⊥ := by
    intro h
    have : w ∈ S := hfix
    rw [h] at this
    exact hw this
  have htop : S = ⊤ := (eq_bot_or_eq_top S).resolve_left hS
  intro g v
  have hv : v ∈ S := by rw [htop]; trivial
  exact hv g

end GeneralField

end Representation
