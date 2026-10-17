/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodeLocalization
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Detecting node ideals supported on one branch

When an ideal vanishes on one full branch, its image on the other full branch
uniquely determines it. This keeps the entire ideal, including nilpotents, and
does not assert the false general claim that normalization detects all ideals.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.PolygonNodeBranchIdealDetection
open PolygonNodeEqualizer PolygonNodeLocalization
variable {R : Type*} [CommRing R]

/-- An ideal with zero second-branch image is determined by its first-branch image. -/
theorem eq_of_second_zero {I J : Ideal (A (R := R))}
    (hI : I.map second.toRingHom = ⊥) (hJ : J.map second.toRingHom = ⊥)
    (h : I.map first.toRingHom = J.map first.toRingHom) : I = J := by
  have lift_mem {L M : Ideal (A (R := R))}
      (hL : L.map second.toRingHom = ⊥) (hM : M.map second.toRingHom = ⊥)
      (he : L.map first.toRingHom = M.map first.toRingHom) : L ≤ M := by
    intro a ha
    have ha' : first a ∈ M.map first.toRingHom :=
      he ▸ Ideal.mem_map_of_mem first.toRingHom ha
    obtain ⟨b, hb, hab⟩ :=
      (Ideal.mem_map_iff_of_surjective first.toRingHom first_surjective).mp ha'
    have hz {L : Ideal (A (R := R))} (hL : L.map second.toRingHom = ⊥)
        {a : A (R := R)} (ha : a ∈ L) : second a = 0 := by
      have hm := Ideal.mem_map_of_mem second.toRingHom ha
      rwa [hL, Ideal.mem_bot] at hm
    have heq : b = a := Subtype.ext (Prod.ext hab ((hz hM hb).trans (hz hL ha).symm))
    exact heq ▸ hb
  exact le_antisymm (lift_mem hI hJ h) (lift_mem hJ hI h.symm)

/-- An ideal with zero first-branch image is determined by its second-branch image. -/
theorem eq_of_first_zero {I J : Ideal (A (R := R))}
    (hI : I.map first.toRingHom = ⊥) (hJ : J.map first.toRingHom = ⊥)
    (h : I.map second.toRingHom = J.map second.toRingHom) : I = J := by
  have lift_mem {L M : Ideal (A (R := R))}
      (hL : L.map first.toRingHom = ⊥) (hM : M.map first.toRingHom = ⊥)
      (he : L.map second.toRingHom = M.map second.toRingHom) : L ≤ M := by
    intro a ha
    have ha' : second a ∈ M.map second.toRingHom :=
      he ▸ Ideal.mem_map_of_mem second.toRingHom ha
    obtain ⟨b, hb, hab⟩ :=
      (Ideal.mem_map_iff_of_surjective second.toRingHom second_surjective).mp ha'
    have hz {L : Ideal (A (R := R))} (hL : L.map first.toRingHom = ⊥)
        {a : A (R := R)} (ha : a ∈ L) : first a = 0 := by
      have hm := Ideal.mem_map_of_mem first.toRingHom ha
      rwa [hL, Ideal.mem_bot] at hm
    have heq : b = a := Subtype.ext (Prod.ext ((hz hM hb).trans (hz hL ha).symm) hab)
    exact heq ▸ hb
  exact le_antisymm (lift_mem hI hJ h) (lift_mem hJ hI h.symm)

/-- Vanishing on both entire branches forces the original node ideal to vanish. -/
theorem eq_bot {I : Ideal (A (R := R))}
    (h₁ : I.map first.toRingHom = ⊥) (h₂ : I.map second.toRingHom = ⊥) : I = ⊥ :=
  eq_of_second_zero h₂ Ideal.map_bot (h₁.trans Ideal.map_bot.symm)

end FLT.Mazur.PolygonNodeBranchIdealDetection
