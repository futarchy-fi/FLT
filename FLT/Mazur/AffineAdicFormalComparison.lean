/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineAdicCohomologyImage
public import FLT.Mazur.AffineModuleEpimorphisms
public import FLT.Mazur.IdealAdicFormalFiniteComparison

/-!
# Bijectivity of the actual formal comparison on an affine scheme in H0

The original H0 image is the ordinary adic filtration, and affine global
sections preserve the actual quotient epimorphism. Thus every finite
comparison is bijective, as is the canonical map on compatible families.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower
open FLT.Mazur.IdealAdicQuotient

universe u

namespace FLT.Mazur.AffineAdicCohomology

variable {R : CommRingCat.{u}} [IsNoetherianRing R]
  (I : (Spec R).IdealSheafData) (M : (Spec R).Modules) [M.IsFinitePresentation]

omit [IsNoetherianRing R] in
/-- The original coordinate ideal satisfies scalar compatibility on every affine open. -/
lemma specScalar_mem (r : R) (hr : r ∈ specIdeal I) (U : (Spec R).affineOpens) :
    (Spec R).presheaf.map U.1.leTop.op ((Scheme.ΓSpecIso R).inv.hom r) ∈ I.ideal U := by
  have hs : (Scheme.ΓSpecIso R).inv.hom r ∈ I.ideal ⟨⊤, isAffineOpen_top _⟩ := by
    have hmap := specIdeal_map I 1
    simp only [pow_one] at hmap
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hr
  exact I.ideal_le_comap_ideal (U := U) (V := ⟨⊤, isAffineOpen_top _⟩)
    (show U.1 ≤ ⊤ from le_top) hs

/-- The actual affine quotient projection is surjective on degree-zero cohomology. -/
lemma projection_hZero_surjective (n : ℕ) :
    Function.Surjective (moduleHMap (projection I M n) 0) := by
  intro y
  obtain ⟨s, hs⟩ := AffineModuleEpimorphisms.surjective_of_epi (projection I M n)
    (moduleH0Equiv (quotient I M n) y)
  refine ⟨(moduleH0Equiv M).symm s, ?_⟩
  apply (moduleH0Equiv (quotient I M n)).injective
  rw [moduleH0Equiv_naturality, LinearEquiv.apply_symm_apply]
  exact hs

/-- The actual finite affine H0 comparison is bijective at every exponent. -/
theorem adicQuotientComparison_hZero_bijective (n : ℕ) :
    Function.Bijective (adicQuotientComparison (Scheme.ΓSpecIso R).inv.hom I M
      (specIdeal I) (specScalar_mem I) 0 n) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      rw [adicQuotientComparison_mk] at hx
      rw [Submodule.Quotient.mk_eq_zero, ← image_eq_adic I M n]
      exact (mem_cohomologyImage_iff _ I M 0 n x).mpr hx
  · intro y
    obtain ⟨x, hx⟩ := projection_hZero_surjective I M n y
    exact ⟨Submodule.Quotient.mk x, hx⟩

/-- The canonical affine H0 formal comparison is bijective, with no completeness assumption. -/
theorem formalComparison_hZero_bijective :
    Function.Bijective (formalComparison (Scheme.ΓSpecIso R).inv.hom I M
      (specIdeal I) (specScalar_mem I) 0) :=
  formalComparison_bijective_of_finite _ I M _ (specScalar_mem I) 0
    (adicQuotientComparison_hZero_bijective I M)

end FLT.Mazur.AffineAdicCohomology
