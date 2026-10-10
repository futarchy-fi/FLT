/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Section lines on a coordinate chart

A line in a coordinate chart is a submodule on which the selected coordinate
is an isomorphism. It has a unique generator with that coordinate equal to one.
Conversely such a generator gives a split rank-one submodule, over any ring.
-/

@[expose] public noncomputable section
universe u v
namespace FLT.Mazur.NormalizedSectionLine
variable (S : Type u) [CommRing S] (ι : Type v)

/-- Restriction of a coordinate functional to an actual submodule. -/
def coordinate (i : ι) (L : Submodule S (ι → S)) : L →ₗ[S] S :=
  (LinearMap.proj i).comp L.subtype

/-- Lines whose projection to the selected coordinate is an isomorphism. -/
abbrev Chart (i : ι) :=
  {L : Submodule S (ι → S) // Function.Bijective (coordinate S ι i L)}

/-- The coordinate trivialization of a line in a chart. -/
def trivialization (i : ι) (L : Chart S ι i) : L.val ≃ₗ[S] S :=
  LinearEquiv.ofBijective (coordinate S ι i L.val) L.property

/-- The unique normalized generator, constructed by the inverse coordinate map. -/
def generator (i : ι) (L : Chart S ι i) : ι → S :=
  (trivialization S ι i L).symm 1

/-- The generator belongs to the original submodule. -/
lemma generator_mem (i : ι) (L : Chart S ι i) : generator S ι i L ∈ L.val :=
  ((trivialization S ι i L).symm 1).property

/-- Its selected coordinate is one. -/
@[simp]
lemma generator_coordinate (i : ι) (L : Chart S ι i) : generator S ι i L i = 1 :=
  (trivialization S ι i L).apply_symm_apply 1

/-- Every vector in the line is its selected coordinate times the generator. -/
lemma eq_smul_generator (i : ι) (L : Chart S ι i) (v : L.val) :
    (v : ι → S) = (v.val i) • generator S ι i L := by
  have h : v = (v.val i) • (trivialization S ι i L).symm 1 := by
    apply (trivialization S ι i L).injective
    simp only [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
    rfl
  exact congrArg Subtype.val h

/-- A normalized tuple generates an actual rank-one submodule with invertible projection. -/
def ofTuple (i : ι) (x : ι → S) (hi : x i = 1) : Chart S ι i := by
  let f := LinearMap.toSpanSingleton S (ι → S) x
  refine ⟨LinearMap.range f, ?_, ?_⟩
  · intro v w h
    obtain ⟨a, ha⟩ := v.property
    obtain ⟨b, hb⟩ := w.property
    have hab : a = b := by
      change v.val i = w.val i at h
      rw [← ha, ← hb] at h
      simpa [f, hi] using h
    apply Subtype.ext
    rw [← ha, ← hb, hab]
  · intro a
    refine ⟨⟨f a, ⟨a, rfl⟩⟩, ?_⟩
    change a * x i = a
    rw [hi, mul_one]

/-- The coordinate functional splits the generating linear map. -/
lemma coordinate_split (i : ι) (x : ι → S) (hi : x i = 1) :
    (LinearMap.proj i).comp (LinearMap.toSpanSingleton S (ι → S) x) =
      LinearMap.id := by
  apply LinearMap.ext
  intro a
  change a * x i = a
  rw [hi, mul_one]

/-- Recovering the normalized generator of a tuple gives that tuple. -/
lemma generator_ofTuple (i : ι) (x : ι → S) (hi : x i = 1) :
    generator S ι i (ofTuple S ι i x hi) = x := by
  let v : (ofTuple S ι i x hi).val :=
    ⟨x, ⟨1, by simp only [LinearMap.toSpanSingleton_apply, one_smul]⟩⟩
  have h := eq_smul_generator S ι i (ofTuple S ι i x hi) v
  simpa only [v, hi, one_smul] using h.symm

/-- Reconstructing the submodule from its generator gives the original line. -/
lemma ofTuple_generator (i : ι) (L : Chart S ι i) :
    ofTuple S ι i (generator S ι i L) (generator_coordinate S ι i L) = L := by
  apply Subtype.ext
  apply le_antisymm
  · rintro v ⟨a, rfl⟩
    exact L.val.smul_mem a (generator_mem S ι i L)
  · intro v hv
    exact ⟨v i, (eq_smul_generator S ι i L ⟨v, hv⟩).symm⟩

/-- Normalized tuples classify the actual section lines in one coordinate chart. -/
def tupleEquiv (i : ι) : {x : ι → S // x i = 1} ≃ Chart S ι i where
  toFun x := ofTuple S ι i x.val x.property
  invFun L := ⟨generator S ι i L, generator_coordinate S ι i L⟩
  left_inv x := Subtype.ext (generator_ofTuple S ι i x.val x.property)
  right_inv L := ofTuple_generator S ι i L

end FLT.Mazur.NormalizedSectionLine
