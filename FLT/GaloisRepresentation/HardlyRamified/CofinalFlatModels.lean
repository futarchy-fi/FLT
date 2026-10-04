/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.FiniteCoefficientUniverses
public import FLT.Deformations.ProartinianQuotients

/-!
# Testing the integral flat condition on cofinal reductions

Finite-flat models on a cofinal family of open coefficient quotients suffice
for the actual integral flat condition. Smaller finite coefficient quotients
inherit models by the proved quotient construction. This is not a crystalline
comparison theorem and does not choose a compatible system of models.
-/

@[expose] public noncomputable section
open scoped NumberField
open IsDedekindDomain
namespace ThreeAdicPlan

variable {R V : Type*} [CommRing R] [IsLocalRing R]
  [TopologicalSpace R] [IsTopologicalRing R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  (ρ : GaloisRep ℚ R V) (v : HeightOneSpectrum (𝓞 ℚ))

/-- A cofinal set of open reductions detects the actual finite-flat condition. -/
theorem flatAt_iff_cofinal_models {ι : Type*} (I : ι → Ideal R)
    (hopen : ∀ i, IsOpen (I i : Set R))
    (hcofinal : ∀ J : Ideal R, IsOpen (J : Set R) → ∃ i, I i ≤ J)
    (hfinite : ∀ J : Ideal R, IsOpen (J : Set R) → Finite (R ⧸ J)) :
    ρ.IsFlatAt v ↔ ∀ i, (ρ.baseChange (R ⧸ I i)).HasFlatProlongationAt v := by
  refine ⟨fun h i ↦ h.cond (I i) (hopen i), ?_⟩
  intro h
  constructor
  intro J hJ
  obtain ⟨i, hi⟩ := hcofinal J hJ
  let : Finite (R ⧸ J) := hfinite J hJ
  apply finiteFlat_of_finite_coefficients_universes ρ v (I i) _ (h i)
  intro x hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hi hx)

/-- Finite residue coefficients supply finiteness of every open parameter quotient. -/
theorem proartinian_open_quotient_finite {O : Type*} [CommRing O] [IsLocalRing O]
    [Finite (IsLocalRing.ResidueField O)] (U : Deformation.ProartinianCat O)
    (J : Ideal U) (hJ : IsOpen (J : Set U)) : Finite (U ⧸ J) := by
  by_cases htop : J = ⊤
  · subst J
    infer_instance
  · exact Deformation.ProartinianCat.openIdealQuotientFinite U
      (OrderDual.toDual ⟨J, hJ, htop⟩)

end ThreeAdicPlan
