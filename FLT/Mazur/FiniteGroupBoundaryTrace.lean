/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupInvariantRing
public import FLT.Mazur.SectionLiftSourceCertificate

/-!
# Actual boundary lifts of orbit-trace multiples

An equivariant surjection lifts every invariant boundary section after
multiplication by any orbit trace. The lift is the orbit sum of the weighted
source lift. No division by the group order is used.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace FLT.Mazur.FiniteGroupQuotient
variable (G : Type*) [Group G] [Fintype G]
variable {A B : Type*} [CommRing A] [CommRing B]
  [MulSemiringAction G A] [MulSemiringAction G B]

/-- The orbit sum, regarded as an actual invariant source function. -/
def orbitTrace (a : A) : invariantRing G A :=
  ⟨∑ g : G, g • a, fun h ↦ by
    simp only [Finset.smul_sum, ← mul_smul]
    exact Equiv.sum_comp (Equiv.mulLeft h) (fun g : G ↦ g • a)⟩

/-- The boundary restriction between the actual fixed subrings. -/
def boundaryMap (f : A →+* B) (hf : ∀ (g : G) a, f (g • a) = g • f a) :
    invariantRing G A →+* invariantRing G B :=
  lift G B (f.comp (inclusion G A)) (fun g a ↦ by
    change g • f a.val = f a.val
    rw [← hf, a.property g])

omit [Fintype G] in
/-- Boundary restriction retains the original source function. -/
@[simp]
theorem boundaryMap_val (f : A →+* B) (hf : ∀ (g : G) a, f (g • a) = g • f a)
    (a : invariantRing G A) : (boundaryMap G f hf a).val = f a.val := rfl

/-- Orbit traces commute with the actual equivariant boundary restriction. -/
theorem boundaryMap_orbitTrace (f : A →+* B)
    (hf : ∀ (g : G) a, f (g • a) = g • f a) (a : A) :
    boundaryMap G f hf (orbitTrace G a) = orbitTrace G (f a) := by
  apply Subtype.ext
  change f (∑ g : G, g • a) = ∑ g : G, g • f a
  simp only [map_sum, hf]

/-- A weighted orbit sum lifts the trace multiple of every invariant boundary function. -/
theorem boundaryMap_weightedTrace (f : A →+* B)
    (hf : ∀ (g : G) a, f (g • a) = g • f a)
    (t : invariantRing G B) (b : A) (hb : f b = t.val) (a : A) :
    boundaryMap G f hf (orbitTrace G (a * b)) =
      boundaryMap G f hf (orbitTrace G a) * t := by
  apply Subtype.ext
  change f (∑ g : G, g • (a * b)) = f (∑ g : G, g • a) * t.val
  have ht : ∀ g : G, g • t.val = t.val := t.property
  simp only [map_sum, MulSemiringAction.smul_mul, map_mul, hf, hb, ht,
    Finset.sum_mul]

/-- Every orbit trace is an actual lifting multiplier, for arbitrary boundary invariants. -/
theorem orbitTrace_mem_sectionLiftIdeal (f : A →+* B)
    (hf : ∀ (g : G) a, f (g • a) = g • f a) (hs : Function.Surjective f)
    (t : invariantRing G B) (a : A) :
    orbitTrace G a ∈ sectionLiftIdeal (boundaryMap G f hf) t := by
  obtain ⟨b, hb⟩ := hs t.val
  exact ⟨orbitTrace G (a * b), boundaryMap_weightedTrace G f hf t b hb a⟩

end FLT.Mazur.FiniteGroupQuotient
