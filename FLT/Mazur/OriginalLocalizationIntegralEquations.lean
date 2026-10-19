/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.QuasiFiniteMinimalPrimeEquations

/-!
# Integrality on an entire localization from original equations

Generator equations with invertible leading coefficients control every element
of the full localized algebra, including all localization torsion.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalLocalizationIntegralEquations
open Polynomial
variable {R B : Type*} [CommRing R] [CommRing B]
  (s : R →+* B) (M : Submonoid R)
  (L T : Type*) [CommRing L] [CommRing T]
  [Algebra R L] [IsLocalization M L] [Algebra B T] [IsLocalization (M.map s) T]
local notation "τ" => (IsLocalization.map T s M.le_comap_map : L →+* T)

/-- The full localized scalar map retains the original square. -/
theorem map_comp :
    (τ : L →+* T).comp (algebraMap R L) = (algebraMap B T).comp s :=
  IsLocalization.map_comp M.le_comap_map

/-- It suffices to prove integrality for the images of unlocalized numerators. -/
theorem map_integral_of_numerators
    (h : ∀ b : B, (τ).IsIntegralElem (algebraMap B T b)) : (τ).IsIntegral := by
  intro x
  obtain ⟨⟨b, u⟩, hx⟩ := IsLocalization.surj (M.map s) x
  obtain ⟨a, ha, he⟩ := u.property
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv'.mp (IsLocalization.map_units L ⟨a, ha⟩)
  have hv' : τ v * algebraMap B T u.val = 1 := by
    have hh := congrArg τ hv
    rw [map_mul, map_one] at hh
    have heq : τ (algebraMap R L a) = algebraMap B T (s a) :=
      congrArg (fun f : R →+* T ↦ f a) (map_comp s M L T)
    rwa [heq, he] at hh
  exact RingHom.IsIntegralElem.of_mul_unit τ x (algebraMap B T u.val) v hv'
    (hx.symm ▸ h b)

/-- Polynomial tests on algebra generators construct integrality on the full localization. -/
theorem map_integral_of_generator_equations (S : Set B)
    (hgen : Subring.closure (Set.range s ∪ S) = ⊤)
    (heq : ∀ b ∈ S, ∃ p : R[X], p.eval₂ s b = 0 ∧ p.leadingCoeff ∈ M) :
    (τ).IsIntegral := by
  apply map_integral_of_numerators
  intro b
  have hb : b ∈ Subring.closure (Set.range s ∪ S) := hgen ▸ Subring.mem_top b
  induction hb using Subring.closure_induction with
  | mem b hb =>
    rcases hb with ⟨r, rfl⟩ | hb
    · have h := (τ).isIntegralElem_map (x := algebraMap R L r)
      have he := congrArg (fun f : R →+* T ↦ f r) (map_comp s M L T)
      change τ (algebraMap R L r) = algebraMap B T (s r) at he
      rwa [he] at h
    · obtain ⟨p, hp, hlead⟩ := heq b hb
      exact s.isIntegralElem_localization_at_leadingCoeff b p hp M hlead
  | zero => simpa only [map_zero] using (τ).isIntegralElem_map (x := 0)
  | one => simpa only [map_one] using (τ).isIntegralElem_map (x := 1)
  | add x y _ _ hx hy => simpa only [map_add] using hx.add τ hy
  | neg x _ hx => simpa only [map_neg] using hx.neg
  | mul x y _ _ hx hy => simpa only [map_mul] using hx.mul τ hy

end FLT.Mazur.OriginalLocalizationIntegralEquations
