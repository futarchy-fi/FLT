/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.ClosedIdealCondition
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Closed equations for trivial action on a specified set

Inertia images need not be chosen generators or a finite set. All matrix
entries of their action minus the identity generate the required closed ideal.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace Deformation.ProartinianCat

universe u
variable {O : Type u} [CommRing O] (U : ProartinianCat O)
  {G n : Type*} [Group G] [Fintype n] [DecidableEq n]
  (ρ : G →* GL n U) (S : Set G)

/-- Impose the identity matrix on every element of the specified set. -/
def framedTrivialityIdeal : Ideal U :=
  (Ideal.span (Set.range fun t : S × n × n ↦
    ρ t.1.val t.2.1 t.2.2 - (1 : Matrix n n U) t.2.1 t.2.2)).closure

/-- The ideal of trivial-action equations is closed. -/
theorem framedTrivialityIdeal_closed : IsClosed (framedTrivialityIdeal U ρ S : Set U) :=
  isClosed_closure

/-- Killing the ideal is exactly the entrywise identity condition. -/
theorem kills_framedTrivialityIdeal_iff {A : ProartinianCat O} (f : U ⟶ A) :
    KillsClosedIdeal U (framedTrivialityIdeal U ρ S) f ↔
      ∀ g ∈ S, ∀ i j, f.hom (ρ g i j) = (1 : Matrix n n A) i j := by
  have hc (i j : n) : f.hom ((1 : Matrix n n U) i j) = (1 : Matrix n n A) i j := by
    simp [Matrix.one_apply]
  have hker : IsClosed (RingHom.ker f.hom.toRingHom : Set U) :=
    isClosed_eq f.hom.cont continuous_const
  have he : framedTrivialityIdeal U ρ S ≤ RingHom.ker f.hom.toRingHom ↔
      Ideal.span (Set.range fun t : S × n × n ↦
        ρ t.1.val t.2.1 t.2.2 - (1 : Matrix n n U) t.2.1 t.2.2) ≤
          RingHom.ker f.hom.toRingHom :=
    ⟨fun h ↦ (show _ ≤ framedTrivialityIdeal U ρ S from
      fun _ hx ↦ subset_closure hx).trans h, fun h ↦ closure_minimal h hker⟩
  rw [KillsClosedIdeal, he, Ideal.span_le]
  constructor
  · intro h g hg i j
    have hz := h (Set.mem_range_self (⟨g, hg⟩, i, j))
    change f.hom (ρ g i j - (1 : Matrix n n U) i j) = 0 at hz
    simpa only [map_sub, hc, sub_eq_zero] using hz
  · intro h z hz
    obtain ⟨⟨⟨g, hg⟩, i, j⟩, rfl⟩ := hz
    change f.hom (ρ g i j - (1 : Matrix n n U) i j) = 0
    rw [map_sub, hc, h g hg i j, sub_self]

/-- The entry equations say precisely that the specialized group action is trivial. -/
theorem kills_framedTrivialityIdeal_iff_map {A : ProartinianCat O} (f : U ⟶ A) :
    KillsClosedIdeal U (framedTrivialityIdeal U ρ S) f ↔
      ∀ g ∈ S, Matrix.GeneralLinearGroup.map f.hom.toRingHom (ρ g) = 1 := by
  rw [kills_framedTrivialityIdeal_iff]
  constructor
  · intro h g hg
    ext i j
    exact h g hg i j
  · intro h g hg i j
    exact congrArg (fun M : GL n A ↦ M i j) (h g hg)

/-- Residual triviality, for example, suffices to prove this ideal proper. -/
theorem framedTrivialityIdeal_ne_top {A : ProartinianCat O} [Nontrivial A] (f : U ⟶ A)
    (hf : ∀ g ∈ S, Matrix.GeneralLinearGroup.map f.hom.toRingHom (ρ g) = 1) :
    framedTrivialityIdeal U ρ S ≠ ⊤ := by
  intro htop
  have hk := (kills_framedTrivialityIdeal_iff_map U ρ S f).mpr hf
  have hz : f.hom 1 = 0 := hk (htop ▸ Submodule.mem_top)
  simp at hz

end Deformation.ProartinianCat
