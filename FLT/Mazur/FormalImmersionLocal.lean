/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# A first-order criterion for surjectivity on complete local rings

Nakayama and adic completeness lift surjectivity modulo the square of the
target maximal ideal to surjectivity of the ring map. Consequently maps
out of the target can be distinguished after precomposition.

This supplies local algebra for the section-separation step in Mazur (1978),
Corollary 4.3. It does not assert the first-order condition for a modular
Jacobian or construct its completed local rings.
-/

@[expose] public section

namespace RingHom

open IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S]

/-- First-order surjectivity forces the source maximal ideal to generate the
target maximal ideal, by Nakayama. -/
theorem map_maximalIdeal_eq_of_surjective_mod_sq (f : R →+* S) [IsLocalHom f]
    (hfg : (maximalIdeal S).FG)
    (hfirst : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal S ^ 2)).comp f)) :
    (maximalIdeal R).map f = maximalIdeal S := by
  apply le_antisymm (map_maximalIdeal_le f)
  apply Submodule.le_of_le_smul_of_le_jacobson_bot hfg
    (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal S) bot_ne_top).ge
  rw [smul_eq_mul, ← pow_two]
  intro x hx
  obtain ⟨a, ha⟩ := hfirst (Ideal.Quotient.mk (maximalIdeal S ^ 2) x)
  have hd : f a - x ∈ maximalIdeal S ^ 2 := Ideal.Quotient.eq.mp ha
  have hfa : f a ∈ maximalIdeal S := by
    have := (maximalIdeal S).add_mem (Ideal.pow_le_self two_ne_zero hd) hx
    simpa using this
  have ha' : a ∈ maximalIdeal R := by
    rw [← maximalIdeal_comap f]
    exact hfa
  have hleft : f a ∈ (maximalIdeal R).map f ⊔ maximalIdeal S ^ 2 :=
    (show (maximalIdeal R).map f ≤ (maximalIdeal R).map f ⊔ maximalIdeal S ^ 2
      from le_sup_left) (Ideal.mem_map_of_mem f ha')
  have hright : f a - x ∈ (maximalIdeal R).map f ⊔ maximalIdeal S ^ 2 :=
    (show maximalIdeal S ^ 2 ≤ (maximalIdeal R).map f ⊔ maximalIdeal S ^ 2
      from le_sup_right) hd
  simpa using (Submodule.sub_mem _ hleft hright)

/-- For a complete source and separated target, first-order surjectivity
implies actual surjectivity. Finite generation is only needed in the target. -/
theorem surjective_of_surjective_mod_maximalIdeal_sq
    (f : R →+* S) [IsLocalHom f]
    [IsPrecomplete (maximalIdeal R) R] [IsHausdorff (maximalIdeal S) S]
    (hfg : (maximalIdeal S).FG)
    (hfirst : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal S ^ 2)).comp f)) :
    Function.Surjective f := by
  have heq := f.map_maximalIdeal_eq_of_surjective_mod_sq hfg hfirst
  have : IsHausdorff ((maximalIdeal R).map f) S := heq ▸ inferInstance
  apply surjective_of_mk_map_comp_surjective (I := maximalIdeal R) f
  rw [heq]
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := hfirst (Ideal.Quotient.mk (maximalIdeal S ^ 2) x)
  refine ⟨a, Ideal.Quotient.eq.mpr ?_⟩
  exact Ideal.pow_le_self two_ne_zero (Ideal.Quotient.eq.mp ha)

/-- Surjectivity on residue fields and cotangent spaces gives surjectivity
on first-order neighborhoods. No completeness is needed for this step. -/
theorem surjective_mod_sq_of_residue_and_cotangent
    (f : R →+* S) [IsLocalHom f]
    (hres : Function.Surjective ((residue S).comp f))
    (hcot : Function.Surjective
      (Ideal.mapCotangent (maximalIdeal R) (maximalIdeal S) f.toIntAlgHom
        (fun x hx ↦ map_nonunit f x hx))) :
    Function.Surjective ((Ideal.Quotient.mk (maximalIdeal S ^ 2)).comp f) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := hres (residue S x)
  have hd : x - f a ∈ maximalIdeal S := by
    apply (residue_eq_zero_iff _).mp
    rw [map_sub]
    exact sub_eq_zero.mpr ha.symm
  obtain ⟨v, hv⟩ := hcot ((maximalIdeal S).toCotangent ⟨x - f a, hd⟩)
  obtain ⟨b, rfl⟩ := (maximalIdeal R).toCotangent_surjective v
  have hb : f b - (x - f a) ∈ maximalIdeal S ^ 2 :=
    (maximalIdeal S).toCotangent_eq.mp hv
  refine ⟨a + b, Ideal.Quotient.eq.mpr ?_⟩
  convert hb using 1
  simp only [map_add]
  ring

/-- The cotangent criterion for a surjective map of complete local rings,
in the case of identical residue fields needed at a rational cusp. -/
theorem surjective_of_residue_and_cotangent
    (f : R →+* S) [IsLocalHom f]
    [IsPrecomplete (maximalIdeal R) R] [IsHausdorff (maximalIdeal S) S]
    (hfg : (maximalIdeal S).FG)
    (hres : Function.Surjective ((residue S).comp f))
    (hcot : Function.Surjective
      (Ideal.mapCotangent (maximalIdeal R) (maximalIdeal S) f.toIntAlgHom
        (fun x hx ↦ map_nonunit f x hx))) :
    Function.Surjective f :=
  f.surjective_of_surjective_mod_maximalIdeal_sq hfg
    (f.surjective_mod_sq_of_residue_and_cotangent hres hcot)

/-- Two maps of completed local rings agreeing after a first-order
surjective local map agree everywhere. -/
theorem comp_injective_of_surjective_mod_maximalIdeal_sq
    (f : R →+* S) [IsLocalHom f]
    [IsPrecomplete (maximalIdeal R) R] [IsHausdorff (maximalIdeal S) S]
    (hfg : (maximalIdeal S).FG)
    (hfirst : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal S ^ 2)).comp f))
    (T : Type*) [CommRing T] :
    Function.Injective (fun g : S →+* T ↦ g.comp f) := by
  intro g h heq
  ext x
  obtain ⟨a, rfl⟩ := f.surjective_of_surjective_mod_maximalIdeal_sq hfg hfirst x
  exact DFunLike.congr_fun heq a

end RingHom
