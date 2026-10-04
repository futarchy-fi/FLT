/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.ClosedIdealCondition

/-!
# Simultaneous closed ideal conditions

The closure of the sum of any family of ideals cuts out their simultaneous
vanishing on continuous maps. Its quotient therefore corepresents simultaneous
ideal conditions. Identifying arithmetic local conditions with these ideals
remains a separate theorem.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace Deformation.ProartinianCat

universe u
variable {O : Type u} [CommRing O] (U : ProartinianCat O)
  {ι : Type*} (I : ι → Ideal U)

/-- Close the sum, since a continuous map to a separated parameter ring kills
the closure of every ideal that it kills. -/
def simultaneousIdeal : Ideal U := (⨆ i, I i).closure

/-- The ideal for simultaneous conditions is closed by construction. -/
theorem simultaneousIdeal_closed : IsClosed (simultaneousIdeal U I : Set U) :=
  isClosed_closure

/-- No extra equation is imposed by taking the closed sum. -/
theorem kills_simultaneousIdeal_iff {A : ProartinianCat O} (f : U ⟶ A) :
    KillsClosedIdeal U (simultaneousIdeal U I) f ↔
      ∀ i, KillsClosedIdeal U (I i) f := by
  have hker : IsClosed (RingHom.ker f.hom.toRingHom : Set U) :=
    isClosed_eq f.hom.cont continuous_const
  constructor
  · intro h i
    exact (le_iSup I i).trans ((show (⨆ i, I i) ≤ simultaneousIdeal U I from
      fun _ hx ↦ subset_closure hx).trans h)
  · intro h
    exact closure_minimal (iSup_le h) hker

/-- A simultaneous solution in a nonzero parameter ring proves the closed sum proper. -/
theorem simultaneousIdeal_ne_top_of_solution {A : ProartinianCat O} [Nontrivial A]
    (f : U ⟶ A) (hf : ∀ i, KillsClosedIdeal U (I i) f) :
    simultaneousIdeal U I ≠ ⊤ := by
  intro htop
  have h := (kills_simultaneousIdeal_iff U I f).mpr hf
  have hz : f.hom 1 = 0 := h (htop ▸ Submodule.mem_top)
  simp at hz

variable [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  (hne : simultaneousIdeal U I ≠ ⊤)

/-- The quotient is formed from the constructed closed sum. -/
def simultaneousIdealQuotient : ProartinianCat O :=
  closedIdealQuotient U (simultaneousIdeal U I) (simultaneousIdeal_closed U I) hne

/-- Its maps classify exactly the simultaneous solutions. -/
def simultaneousIdealFactorEquiv (A : ProartinianCat O) :
    (simultaneousIdealQuotient U I hne ⟶ A) ≃
      {f : U ⟶ A // ∀ i, KillsClosedIdeal U (I i) f} :=
  (closedIdealFactorEquiv U (simultaneousIdeal U I)
    (simultaneousIdeal_closed U I) hne A).trans
    (Equiv.subtypeEquivRight (kills_simultaneousIdeal_iff U I))

omit [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- Imposing the family is equivalent to imposing its single closed-sum condition. -/
theorem simultaneousIdealCondition_obj (A : ProartinianCat O) (f : U ⟶ A) :
    f ∈ (closedIdealCondition U (simultaneousIdeal U I)).obj A ↔
      ∀ i, f ∈ (closedIdealCondition U (I i)).obj A :=
  kills_simultaneousIdeal_iff U I f

end Deformation.ProartinianCat
