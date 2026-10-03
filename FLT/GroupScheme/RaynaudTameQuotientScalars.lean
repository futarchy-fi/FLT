/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCommutativeImageScalars
public import FLT.Deformations.RepresentationTheory.PGroupInvariants

/-!
# Scalar fields after killing wild inertia

A normal subgroup with p-group image fixes a simple finite representation.
A commutative quotient then forces its actual image to commute.
-/

@[expose] public noncomputable section
namespace Representation

universe v w
variable {p : ℕ} [Fact p.Prime] {G : Type w} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
  (ρ : Representation (ZMod p) G V) [IsIrreducible ρ]
  (N : Subgroup G) [N.Normal]

/-- Killing a normal p-group image and passing through a tame quotient derives scalars. -/
theorem exists_rank_one_scalar_field_of_tame_quotient
    (hN : IsPGroup p (ρ.toHomUnits.comp N.subtype).range)
    (hcomm : ∀ a b : G ⧸ N, Commute a b) :
    ∃ (F : Type v) (_ : Field F) (_ : Finite F) (_ : CharP F p) (_ : Module F V),
      Module.finrank F V = 1 ∧ ∀ (a : F) (g : G) (x : V), ρ g (a • x) = a • ρ g x := by
  have hfix := normal_acts_trivially_of_isPGroup_image ρ N hN
  have hker : N ≤ ρ.toHomUnits.ker := by
    intro g hg
    apply Units.ext
    exact LinearMap.ext (hfix ⟨g, hg⟩)
  let f := QuotientGroup.lift N ρ.toHomUnits hker
  apply exists_rank_one_scalar_field_of_commuting ρ _ p
  intro g h
  have heq := (hcomm (QuotientGroup.mk g) (QuotientGroup.mk h)).map f
  exact congrArg Units.val heq.eq

end Representation
