/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupReesIrrelevant

/-!
# A chosen generating family generates the Rees irrelevant ideal

Spanning the original center suffices: the degree-one monomial map preserves
addition and original scalar multiplication. No additional Rees generators
are needed in positive degrees.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A : Type*} [CommRing A] (I : Ideal A)
  {ι : Type*} (g : ι → A) (hg : ∀ i, g i ∈ I)

/-- The degree-one monomial of a sum is the sum of the original monomials. -/
theorem generator_add (a b : A) (ha : a ∈ I) (hb : b ∈ I) :
    generator I (a + b) (I.add_mem ha hb) = generator I a ha + generator I b hb := by
  apply Subtype.ext
  exact map_add (Polynomial.monomial 1) a b

/-- Multiplying a center element by an original scalar preserves its degree-one monomial. -/
theorem generator_smul (r a : A) (ha : a ∈ I) :
    generator I (r • a) (I.smul_mem r ha) = r • generator I a ha := by
  apply Subtype.ext
  exact (Polynomial.monomial 1).map_smul r a

/-- An ideal containing a generating family's monomials contains every center monomial. -/
theorem generator_mem_of_span (hspan : Ideal.span (Set.range g) = I)
    (J : Ideal (reesAlgebra I)) (hJ : ∀ i, generator I (g i) (hg i) ∈ J)
    (a : A) (ha : a ∈ I) : generator I a ha ∈ J := by
  have hspan' : a ∈ Ideal.span (Set.range g) := hspan.symm ▸ ha
  suffices h : ∀ ha : a ∈ I, generator I a ha ∈ J from h ha
  refine Submodule.span_induction (p := fun a _ => ∀ ha : a ∈ I,
    generator I a ha ∈ J) ?_ ?_ ?_ ?_ hspan'
  · intro a ha
    obtain ⟨i, rfl⟩ := ha
    exact fun _ => hJ i
  · intro hzero
    have he : generator I 0 hzero = 0 := Subtype.ext (map_zero (Polynomial.monomial 1))
    rw [he]
    exact J.zero_mem
  · intro a b ha hb iha ihb hab
    have haI : a ∈ I := hspan ▸ ha
    have hbI : b ∈ I := hspan ▸ hb
    rw [generator_add I a b haI hbI]
    exact J.add_mem (iha haI) (ihb hbI)
  · intro r a ha ih hra
    have haI : a ∈ I := hspan ▸ ha
    rw [generator_smul I r a haI]
    exact (J.restrictScalars A).smul_mem r (ih haI)

/-- Any family spanning the original center generates the full Rees irrelevant ideal. -/
theorem irrelevant_eq_span_of_span (hspan : Ideal.span (Set.range g) = I) :
    (HomogeneousIdeal.irrelevant (component I)).toIdeal =
      Ideal.span (Set.range (fun i => generator I (g i) (hg i))) := by
  apply le_antisymm
  · apply irrelevant_le_of_generators
    exact generator_mem_of_span I g hg hspan _ fun i => Ideal.subset_span ⟨i, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact HomogeneousIdeal.mem_irrelevant_of_mem (component I) (by decide : 0 < 1)
      (generator_mem I (g i) (hg i))

end FLT.Mazur.BlowupRees
