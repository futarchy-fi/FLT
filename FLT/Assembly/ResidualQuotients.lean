/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.LatticeHardlyRamified
public import FLT.GaloisRepresentation.HardlyRamified.ModThreeSorted
public import FLT.GaloisRepresentation.HardlyRamified.RibetAdapters

/-!
# Integral sorting supplies the residual input for every stable lattice

Transport the coefficient-linear mod-three quotient to the algebraic reduction
used by Ribet's lemma. The normalized integral model gives this quotient for
every stable lattice in its generic fibre.
-/

@[expose] public noncomputable section

open scoped TensorProduct ThreeAdicPlan
open IsLocalRing GaloisRepresentation

namespace ThreeAdicPlan

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Lattices

variable {O K W : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W]
  [TopologicalSpace O] [IsTopologicalRing O]
  [TopologicalSpace K] [IsTopologicalRing K]
  [Algebra ℤ_[3] O] [Finite (ResidueField O)]
  [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
  [IsTopologicalRing (ResidueField O)] [ContinuousSMul O (ResidueField O)]

/-- Integral sorting gives a trivial quotient of the algebraic stable-lattice reduction. -/
theorem residual_quotient_of_sortedExtensionExists
    (hsorted : SortedExtensionExists)
    (ρK : GaloisRep ℚ K W) (Λ : Submodule O W)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K))
    (hred : HardlyRamifiedReduction (by decide : Odd 3) ρK Λ hΛ hOK) :
    ∃ π : StableLattice.Reduction O W Λ →ₗ[ResidueField O] ResidueField O,
      Function.Surjective π ∧
        ∀ g v, π (StableLattice.reducedRep ρK.toRepresentation Λ hΛ.stable g v) = π v := by
  let instLattice := hΛ.isLattice
  obtain ⟨hdim, e, hρ, he⟩ := hred
  obtain ⟨π, hπ, hinv⟩ := hρ.mod_three_of_sortedExtensionExists hsorted _ hdim
  refine ⟨π.comp e.symm.toLinearMap, hπ.comp e.symm.surjective, ?_⟩
  intro g v
  change π (e.symm (StableLattice.reducedRep ρK.toRepresentation Λ hΛ.stable g v)) =
    π (e.symm v)
  rw [← e.apply_symm_apply v, ← he, e.symm_apply_apply]
  simpa only [e.symm_apply_apply] using hinv g (e.symm v)

/-- With hardly ramified reductions on every lattice, integral sorting forces reducibility. -/
theorem not_isIrreducible_of_sortedExtensionExists
    [FiniteDimensional K W] [IsAdicComplete (maximalIdeal O) O]
    (hsorted : SortedExtensionExists)
    (ρK : GaloisRep ℚ K W) (hdim : Module.finrank K W = 2)
    (Λ₀ : Submodule O W)
    (h₀ : StableLattice.IsStableLattice ρK.toRepresentation Λ₀)
    (hOK : Topology.IsInducing (algebraMap O K))
    (hred : ∀ (Λ : Submodule O W)
      (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ),
      HardlyRamifiedReduction (by decide : Odd 3) ρK Λ hΛ hOK) :
    ¬ ρK.toRepresentation.IsIrreducible := by
  let instLattice := h₀.isLattice
  let instCharThree : CharP (ResidueField O) 3 :=
    charP_three_of_finite_padic_algebra (ResidueField O)
  obtain ⟨hdim₀, e, hr, he⟩ := hred Λ₀ h₀
  let instFiniteReduction :
      FiniteDimensional (ResidueField O) (StableLattice.Reduction O W Λ₀) :=
    Module.Finite.equiv e
  let τ := StableLattice.reducedRep ρK.toRepresentation Λ₀ h₀.stable
  let χ := (LinearMap.det.comp τ).toHomUnits
  have hdimτ : Module.finrank (ResidueField O) (StableLattice.Reduction O W Λ₀) = 2 := by
    rw [← e.finrank_eq]
    exact Module.finrank_eq_of_rank_eq hdim₀
  have hconj (g : Field.absoluteGaloisGroup ℚ) :
      τ g = e.conj (((latticeGaloisRep ρK Λ₀ h₀ hOK).baseChange (ResidueField O)) g) := by
    apply LinearMap.ext
    intro v
    change τ g v = e (((latticeGaloisRep ρK Λ₀ h₀ hOK).baseChange
      (ResidueField O)) g (e.symm v))
    exact (congrArg (τ g) (e.apply_symm_apply v)).symm.trans (he g (e.symm v)).symm
  have hne : ∃ g, χ g ≠ 1 := by
    refine ⟨rationalComplexConjugation, ?_⟩
    intro hc
    have hd := hr.det rationalComplexConjugation
    have hdχ : (χ rationalComplexConjugation : ResidueField O) = -1 := by
      change LinearMap.det (τ rationalComplexConjugation) = -1
      rw [hconj, e.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj]
      change ((latticeGaloisRep ρK Λ₀ h₀ hOK).baseChange (ResidueField O)).det
        rationalComplexConjugation = -1
      rw [hd, rationalComplexConjugation_cyclotomic, map_neg, map_one]
    rw [hc, Units.val_one] at hdχ
    have hthree : (3 : ResidueField O) = 0 := CharP.cast_eq_zero _ 3
    have hone : (1 : ResidueField O) = 0 := by linear_combination hthree - hdχ
    exact one_ne_zero hone
  obtain ⟨π, hπ, hπG⟩ := residual_quotient_of_sortedExtensionExists
    hsorted ρK Λ₀ h₀ hOK (hred Λ₀ h₀)
  have hss : StableLattice.HasSemisimplification τ 1 χ :=
    Or.inr (StableLattice.isExtensionOf_of_trivial_quotient τ hdimτ χ
      (fun _ ↦ rfl) π hπ hπG)
  exact StableLattice.not_isIrreducible_of_all_lattices_trivial_quotient
    ρK.toRepresentation hdim Λ₀ h₀ χ hne hss
    (fun Λ hΛ ↦ residual_quotient_of_sortedExtensionExists
      hsorted ρK Λ hΛ hOK (hred Λ hΛ))

end Lattices

end ThreeAdicPlan
