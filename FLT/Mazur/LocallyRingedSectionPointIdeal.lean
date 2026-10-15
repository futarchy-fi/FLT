/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RingedSpaceIdealLocus

/-!
# Point primes and ideal unit loci

The prime associated to a point is the inverse image of its stalk maximal
ideal. Failure of an ideal's unit locus to cover that point is exactly
containment in this prime. This uses actual points of the locally ringed
space and does not identify that space with the spectrum of its sections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur
universe u
variable (X : LocallyRingedSpace.{u}) (W : Opens X)

/-- The prime of sections noninvertible at the specified actual point. -/
def sectionPointIdeal (x : W) : Ideal (X.presheaf.obj (op W)) :=
  (IsLocalRing.maximalIdeal (X.presheaf.stalk x.val)).comap
    (X.presheaf.germ W x.val x.property).hom

/-- Contraction of the stalk maximal ideal is prime. -/
instance sectionPointIdeal_isPrime (x : W) : (sectionPointIdeal X W x).IsPrime :=
  Ideal.comap_isPrime _ _

/-- Membership in the point prime means failure to be a unit at that point. -/
theorem mem_sectionPointIdeal (x : W) (s : X.presheaf.obj (op W)) :
    s ∈ sectionPointIdeal X W x ↔ x.val ∉ X.toRingedSpace.basicOpen s := by
  rw [X.toRingedSpace.mem_basicOpen s x.val x.property]
  exact Iff.rfl

/-- The missing points of the ideal unit locus are exactly the containing point primes. -/
theorem notMem_sectionIdealOpen_iff (I : Ideal (X.presheaf.obj (op W))) (x : W) :
    x.val ∉ sectionIdealOpen X.toRingedSpace W I ↔ I ≤ sectionPointIdeal X W x := by
  rw [mem_sectionIdealOpen]
  constructor
  · intro h s hs
    exact (mem_sectionPointIdeal X W x s).mpr fun hx ↦ h ⟨s, hs, hx⟩
  · rintro h ⟨s, hs, hx⟩
    exact (mem_sectionPointIdeal X W x s).mp (h hs) hx

/-- Covering the original domain is equivalent to escaping every actual point prime. -/
theorem sectionIdealOpen_eq_domain_iff (I : Ideal (X.presheaf.obj (op W))) :
    sectionIdealOpen X.toRingedSpace W I = W ↔
      ∀ x : W, ¬ I ≤ sectionPointIdeal X W x := by
  constructor
  · intro h x hx
    have hn := (notMem_sectionIdealOpen_iff X W I x).mpr hx
    exact hn (h.symm ▸ x.property)
  · intro h
    apply le_antisymm (sectionIdealOpen_le X.toRingedSpace W I)
    intro x hx
    by_contra hn
    exact h ⟨x, hx⟩ ((notMem_sectionIdealOpen_iff X W I ⟨x, hx⟩).mp hn)

end FLT.Mazur
