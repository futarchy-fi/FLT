/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.InertiaTwoSquareZero

/-! # Square-zero inertia at two for every odd-prime hardly ramified representation -/

@[expose] public noncomputable section
open GaloisRepresentation

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan

/-- The HR determinant is one on inertia at two. -/
theorem hardlyRamified_det_on_inertiaTwo_general
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    {O M : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [IsLocalRing O] [Algebra ℤ_[p] O] [AddCommGroup M] [Module O M]
    [Module.Free O M] [Module.Finite O M]
    (hdim : Module.rank O M = 2) (ρ : GaloisRep ℚ O M)
    (hρ : GaloisRepresentation.IsHardlyRamified hpodd hdim ρ)
    (g : Field.absoluteGaloisGroup (twoAdicPlace.adicCompletion ℚ))
    (hg : g ∈ localInertiaGroup twoAdicPlace) :
    LinearMap.det (ρ (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) g)) = 1 := by
  rw [show LinearMap.det (ρ (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) g)) = _ from hρ.det _]
  rw [cyclotomicCharacter_localInertia p 2 (by decide) (by
    intro h; subst p; exact (by decide : ¬ Odd 2) hpodd) g hg, map_one]

/-- The unramified quotient at two and the cyclotomic determinant in HR
force square-zero inertia for the number-field completion definition. -/
theorem hardlyRamified_inertiaTwo_sq_zero_general
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    {O M : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M]
    (hdim : Module.rank O M = 2) (ρ : GaloisRep ℚ O M)
    (hρ : GaloisRepresentation.IsHardlyRamified hpodd hdim ρ)
    (g : Field.absoluteGaloisGroup (twoAdicPlace.adicCompletion ℚ))
    (hg : g ∈ localInertiaGroup twoAdicPlace) :
    (ρ (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) g) - 1) ^ 2 = 0 := by
  obtain ⟨h, hh, a, ha⟩ := localInertiaTwo_transport g hg
  obtain ⟨π, hπ, δ, hδ⟩ := hρ.isTameAtTwo
  have hhδ : δ h = 1 := (hδ 1 0).2.1 hh
  let π' : M →ₗ[O] O := π.comp (ρ a)
  have hs : Function.Surjective (ρ a) := by
    intro x
    refine ⟨ρ a⁻¹ x, ?_⟩
    change (ρ a * ρ a⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  apply sub_one_sq_eq_zero_of_trivial_quotient (Module.finrank_eq_of_rank_eq hdim)
    _ π' (hπ.comp hs) _ (hardlyRamified_det_on_inertiaTwo_general hpodd hdim ρ hρ g hg)
  intro x
  have he : ρ a (ρ (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) g) x) =
      ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) h) (ρ a x) := by
    have he := congrArg (fun k : Field.absoluteGaloisGroup ℚ ↦ ρ k x) ha
    simpa only [map_mul, Module.End.mul_apply] using he
  change π (ρ a (ρ _ x)) = π (ρ a x)
  rw [he]
  have hquot := (hδ h (ρ a x)).1
  rw [hhδ] at hquot
  convert hquot using 1
  congr 3


end ThreeAdicPlan
