/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.FramedDeterminantIdeal
public import FLT.Deformations.FramedQuotientIdeal
public import FLT.Deformations.FramedTrivialityIdeal

/-!
# Simultaneous determinant, inertia and local quotient equations

This closed sum enforces three actual matrix conditions. No finite-flat or
characteristic-zero existence assertion is built into the construction.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace Deformation.ProartinianCat

universe u
variable {O : Type u} [CommRing O] (U : ProartinianCat O)
  {G n H : Type*} [Group G] [Group H] [Fintype n] [DecidableEq n]
  (ρ : G →* GL n U) (δ : G → O) (S : Set G) (ι : H →* G) (χ : H →* Oˣ) (q : n)

/-- The closed sum of the three explicitly constructed equation ideals. -/
def framedArithmeticIdeal : Ideal U :=
  ((framedDeterminantIdeal U ρ δ ⊔ framedTrivialityIdeal U ρ S) ⊔
    framedQuotientIdeal U (ρ.comp ι) χ q).closure

/-- The simultaneous ideal is closed. -/
theorem framedArithmeticIdeal_closed :
    IsClosed (framedArithmeticIdeal U ρ δ S ι χ q : Set U) := isClosed_closure

/-- There are no additional continuous equations beyond the three stated conditions. -/
theorem kills_framedArithmeticIdeal_iff {A : ProartinianCat O} (f : U ⟶ A) :
    KillsClosedIdeal U (framedArithmeticIdeal U ρ δ S ι χ q) f ↔
      (∀ g, f.hom (ρ g : Matrix n n U).det = algebraMap O A (δ g)) ∧
      (∀ g ∈ S, Matrix.GeneralLinearGroup.map f.hom.toRingHom (ρ g) = 1) ∧
      (∀ g j, f.hom (ρ (ι g) q j) =
        if j = q then algebraMap O A (χ g : O) else 0) := by
  have hker : IsClosed (RingHom.ker f.hom.toRingHom : Set U) :=
    isClosed_eq f.hom.cont continuous_const
  have he : KillsClosedIdeal U (framedArithmeticIdeal U ρ δ S ι χ q) f ↔
      (KillsClosedIdeal U (framedDeterminantIdeal U ρ δ) f ∧
        KillsClosedIdeal U (framedTrivialityIdeal U ρ S) f) ∧
          KillsClosedIdeal U (framedQuotientIdeal U (ρ.comp ι) χ q) f := by
    change Ideal.closure _ ≤ _ ↔ (_ ≤ _ ∧ _ ≤ _) ∧ _ ≤ _
    rw [← sup_le_iff, ← sup_le_iff]
    exact ⟨fun h ↦ (show _ ≤ Ideal.closure _ from fun _ hx ↦ subset_closure hx).trans h,
      fun h ↦ closure_minimal h hker⟩
  rw [he, kills_framedDeterminantIdeal_iff, kills_framedTrivialityIdeal_iff_map,
    kills_framedQuotientIdeal_iff, and_assoc]
  rfl

/-- A common residual solution proves the simultaneous ideal proper. -/
theorem framedArithmeticIdeal_ne_top {A : ProartinianCat O} [Nontrivial A] (f : U ⟶ A)
    (hdet : ∀ g, f.hom (ρ g : Matrix n n U).det = algebraMap O A (δ g))
    (htriv : ∀ g ∈ S, Matrix.GeneralLinearGroup.map f.hom.toRingHom (ρ g) = 1)
    (hrow : ∀ g j, f.hom (ρ (ι g) q j) =
      if j = q then algebraMap O A (χ g : O) else 0) :
    framedArithmeticIdeal U ρ δ S ι χ q ≠ ⊤ := by
  intro htop
  have hk := (kills_framedArithmeticIdeal_iff U ρ δ S ι χ q f).mpr ⟨hdet, htriv, hrow⟩
  have hz : f.hom 1 = 0 := hk (htop ▸ Submodule.mem_top)
  simp at hz

end Deformation.ProartinianCat
