/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateGroupEquivalence

/-!
# Tate vanishing on all finite subgroups

The subgroup-wise condition is stable under restriction. The comparison uses
actual group reindexing, including the norm differential.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G]

/-- Tate vanishing in a fixed degree on every finite subgroup. -/
def SubgroupTateVanishing (M : Rep k G) (n : ℤ) : Prop :=
  ∀ (H : Subgroup G) [Fintype H], Limits.IsZero (tateCohomology (Rep.res H.subtype M) n)

/-- Vanishing on all finite subgroups is inherited by any subgroup. -/
theorem SubgroupTateVanishing.res {M : Rep k G} {n : ℤ}
    (h : SubgroupTateVanishing M n) (N : Subgroup G) :
    SubgroupTateVanishing (Rep.res N.subtype M) n := by
  intro H _
  let e := H.equivMapOfInjective N.subtype N.subtype_injective
  let : Fintype (H.map N.subtype) := Fintype.ofEquiv H e.toEquiv
  exact (h (H.map N.subtype)).of_iso
    (tateGroupEquivalenceIso (Rep.res (H.map N.subtype).subtype M) e n).symm

/-- On a finite group the subgroup condition includes the group itself. -/
theorem SubgroupTateVanishing.self [Fintype G] {M : Rep k G} {n : ℤ}
    (h : SubgroupTateVanishing M n) : Limits.IsZero (tateCohomology M n) := by
  let : Fintype (⊤ : Subgroup G) := Fintype.ofFinite _
  exact (h ⊤).of_iso
    (tateGroupEquivalenceIso (Rep.res (⊤ : Subgroup G).subtype M)
      (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm n).symm

end LocalClassFieldTheory
