/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.FiniteType

/-!
# Extending a generic ring map by testing finitely many generators

A scalar-compatible map into a larger ring descends to an embedded ring once
its finitely many algebra generators descend. Failure supplies an actual
non-descending generator, rather than an assumed extension map.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteGeneratorRingLift
variable {R B V K : Type*} [CommRing R] [CommRing B] [CommRing V] [CommRing K]
  (s : R →+* B) (a : Finset B)
  (ha : Subring.closure (Set.range s ∪ (a : Set B)) = ⊤)

include ha in
/-- Membership in a subring can be checked on the scalars and the chosen finite generators. -/
theorem range_le (φ : B →+* K) (C : Subring K)
    (hs : ∀ r, φ (s r) ∈ C) (hg : ∀ b ∈ a, φ b ∈ C) :
    ∀ b, φ b ∈ C := by
  have h : Subring.closure (Set.range s ∪ (a : Set B)) ≤ C.comap φ := by
    apply Subring.closure_le.mpr
    rintro b (⟨r, rfl⟩ | hb)
    · exact hs r
    · exact hg b hb
  rw [ha] at h
  exact fun b ↦ h (show b ∈ (⊤ : Subring B) from trivial)

/-- An injective ring map admits a factorization of every map landing in its range. -/
theorem exists_factor (j : V →+* K) (hj : Function.Injective j) (φ : B →+* K)
    (hφ : ∀ b, φ b ∈ j.range) :
    ∃ l : B →+* V, j.comp l = φ := by
  let e : V ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun x y h ↦ hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  let l := e.symm.toRingHom.comp (φ.codRestrict j.range hφ)
  refine ⟨l, ?_⟩
  ext b
  exact congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict j.range hφ b))

include ha in
/-- Finite generator values construct a full lift preserving the original scalar map. -/
theorem exists_lift (j : V →+* K) (hj : Function.Injective j)
    (φ : B →+* K) (t : R →+* V) (hcomm : φ.comp s = j.comp t)
    (hg : ∀ b ∈ a, φ b ∈ j.range) :
    ∃ l : B →+* V, j.comp l = φ ∧ l.comp s = t := by
  have hs (r : R) : φ (s r) ∈ j.range := by
    rw [show φ (s r) = j (t r) from DFunLike.congr_fun hcomm r]
    exact ⟨t r, rfl⟩
  obtain ⟨l, hl⟩ := exists_factor j hj φ (range_le s a ha φ j.range hs hg)
  refine ⟨l, hl, ?_⟩
  ext r
  apply hj
  exact (DFunLike.congr_fun hl (s r)).trans (DFunLike.congr_fun hcomm r)

include ha in
/-- A failure to extend has a witness among the same finite generators. -/
theorem exists_generator_outside (j : V →+* K) (hj : Function.Injective j)
    (φ : B →+* K) (t : R →+* V) (hcomm : φ.comp s = j.comp t)
    (h : ¬ ∃ l : B →+* V, j.comp l = φ ∧ l.comp s = t) :
    ∃ b ∈ a, φ b ∉ j.range := by
  by_contra hn
  push Not at hn
  exact h (exists_lift s a ha j hj φ t hcomm hn)

end FLT.Mazur.FiniteGeneratorRingLift
