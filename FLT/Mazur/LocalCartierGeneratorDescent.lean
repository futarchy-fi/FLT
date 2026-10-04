/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.RingTheory.LocalRing.IdealGeneratorDescent
public import Mathlib.RingTheory.Finiteness.Descent

/-!
# Descent of regular principal ideals along flat local maps

Finite generation is descended, rather than assumed. A descended generator
is regular because its image divides the given regular generator and the
faithfully flat algebra map is injective. This is the local-ring input to
Cartier descent, not the missing passage from stalks to affine neighborhoods.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FCurve

/-- Every generator of an ideal containing a regular element is regular. -/
lemma isRegular_of_mem_span_singleton {R : Type*} [CommRing R]
    {a b : R} (hb : IsRegular b) (h : b ∈ Ideal.span {a}) : IsRegular a := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp h
  exact hb.of_mul_left

/-- An injective ring map detects regularity of any element with regular image. -/
lemma isRegular_of_injective_ringHom {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (a : R)
    (ha : IsRegular (f a)) : IsRegular a := by
  rw [← isLeftRegular_iff_isRegular]
  intro x y h
  apply hf
  apply ha.left
  simpa only [map_mul] using congrArg f h

/-- A regular principal ideal after a flat local extension was already regular principal. -/
theorem exists_regular_generator_of_flat_local {R S : Type*}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (I : Ideal R) (b : S) (hb : IsRegular b)
    (hI : I.map (algebraMap R S) = Ideal.span {b}) :
    ∃ a : R, IsRegular a ∧ I = Ideal.span {a} := by
  let : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hfg : I.FG := Ideal.FG.of_FG_map_of_faithfullyFlat (S := S)
    (hI ▸ Submodule.fg_span_singleton b)
  let : Module.Finite R I := Module.Finite.of_fg hfg
  have hv : I.map (algebraMap R S) = Ideal.span (Set.range (fun _ : Fin 1 ↦ b)) := by
    simpa only [Set.range_const] using hI
  obtain ⟨rs, hrs, he⟩ := Ideal.exists_ofList_of_map_eq_span S I (fun _ : Fin 1 ↦ b) hv
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hrs
  have haI : I = Ideal.span {a} := by simpa [Ideal.ofList] using he.symm
  have hbmem : b ∈ Ideal.span {algebraMap R S a} := by
    have : b ∈ I.map (algebraMap R S) := hI ▸ Ideal.subset_span (Set.mem_singleton b)
    simpa only [haI, Ideal.map_span, Set.image_singleton] using this
  exact ⟨a, isRegular_of_injective_ringHom (algebraMap R S)
    (FaithfulSMul.algebraMap_injective R S) a
    (isRegular_of_mem_span_singleton hb hbmem), haI⟩

end FLT.Mazur.FCurve
