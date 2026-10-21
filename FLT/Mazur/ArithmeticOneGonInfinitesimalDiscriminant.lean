/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonParameter
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# The discriminant detects infinitesimal arithmetic parameters

Near the parameter-zero boundary the actual discriminant determines every
nilpotent parameter, in all characteristics. Every square-zero discriminant
has a unique nilpotent parameter in this explicit family.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ArithmeticOneGonParameter
open OneGonSmoothing
variable {R : Type} [CommRing R]

/-- The difference factor for two infinitesimal parameters is invertible. -/
theorem nilpotent_difference_factor {s t : R} (hs : IsNilpotent s) (ht : IsNilpotent t) :
    IsUnit (1 + 432 * (s + t)) :=
  ((Commute.all 432 (s + t)).isNilpotent_mul_left
    ((Commute.all s t).isNilpotent_add hs ht)).isUnit_one_add

/-- Equal discriminants detect the exact original nilpotent arithmetic parameter. -/
theorem nilpotent_discriminant_injective {s t : R}
    (hs : IsNilpotent s) (ht : IsNilpotent t)
    (h : (equation s).Δ = (equation t).Δ) : s = t := by
  have he : (s - t) * (1 + 432 * (s + t)) = 0 := by
    calc
      _ = (equation t).Δ - (equation s).Δ := by
        rw [equation_discriminant, equation_discriminant]
        ring
      _ = 0 := by rw [h, sub_self]
  exact sub_eq_zero.mp ((nilpotent_difference_factor hs ht).mul_left_eq_zero.mp he)

/-- Full classifying homomorphisms near the boundary are determined by their discriminants. -/
theorem infinitesimal_hom_ext (f g : ParameterRing →+* R)
    (hf : IsNilpotent (f parameter)) (hg : IsNilpotent (g parameter))
    (h : f (equation parameter).Δ = g (equation parameter).Δ) : f = g := by
  apply hom_ext
  apply nilpotent_discriminant_injective hf hg
  simpa only [← WeierstrassCurve.map_Δ, equation_map] using h

/-- Every first-order discriminant gives a unique infinitesimal arithmetic parameter. -/
theorem exists_unique_squareZero_discriminant (d : R) (hd : d ^ 2 = 0) :
    ∃! t : {t : R // IsNilpotent t}, (equation t.val).Δ = d := by
  have hn : IsNilpotent d := ⟨2, hd⟩
  have he : (equation (-d)).Δ = d := by
    rw [equation_discriminant]
    calc
      _ = d - 432 * d ^ 2 := by ring
      _ = d := by rw [hd, mul_zero, sub_zero]
  refine ⟨⟨-d, hn.neg⟩, he, ?_⟩
  intro t ht
  exact Subtype.ext (nilpotent_discriminant_injective t.property hn.neg (ht.trans he.symm))

end FLT.Mazur.ArithmeticOneGonParameter
