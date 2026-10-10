/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicCohomologyReconstruction
public import FLT.Mazur.IdealAdicCompatibleLifting

/-!
# Algebraizing compatible sections over a complete Noetherian base

Proper formal functions reconstructs actual global sections, with their
original quotient projections. Graded H1 vanishing gives finite-level lifts.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening FLT.Mazur.Chow.AffineBase
open FLT.Mazur.FCurve FLT.Mazur.IdealAdicQuotient

namespace FLT.Mazur.BaseAdicCohomology

variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  {X : Scheme.{0}} [X.IsSeparated] (f : X ⟶ Spec R) [IsProper f] (J : Ideal R)
  [IsAdicComplete J R] (M : X.Modules) [M.IsFinitePresentation]

/-- A compatible system of actual quotient sections has a unique actual global section. -/
theorem existsUnique_globalSection :
    let _ := Chow.source_isNoetherian f
    ∀ s : ∀ n, Γ(quotient ((baseIdeal R J).comap f) M n, ⊤),
      (∀ a b (hab : a ≤ b), (reduction ((baseIdeal R J).comap f) M hab).app ⊤ (s b) = s a) →
      ∃! t : Γ(M, ⊤), ∀ n, (projection ((baseIdeal R J).comap f) M n).app ⊤ t = s n := by
  let _ := Chow.source_isNoetherian f
  dsimp only
  intro s hs
  let I := (baseIdeal R J).comap f
  let x : compatibleCohomology (baseCohomologyScalars f) I M 0 :=
    ⟨fun n ↦ (moduleH0Equiv (quotient I M n)).symm (s n), by
      intro a b hab
      change moduleHMap (reduction I M hab) 0
        ((moduleH0Equiv (quotient I M b)).symm (s b)) =
          (moduleH0Equiv (quotient I M a)).symm (s a)
      apply (moduleH0Equiv (quotient I M a)).injective
      rw [moduleH0Equiv_naturality]
      simpa only [LinearEquiv.apply_symm_apply] using hs a b hab⟩
  obtain ⟨y, hy, hu⟩ := existsUnique_cohomologyClass f J M 0 x
  refine ⟨moduleH0Equiv M y, ?_, ?_⟩
  · intro n
    rw [← moduleH0Equiv_naturality, hy n]
    exact (moduleH0Equiv (quotient I M n)).apply_symm_apply (s n)
  · intro z hz
    have he : (moduleH0Equiv M).symm z = y := by
      apply hu
      intro n
      apply (moduleH0Equiv (quotient I M n)).injective
      rw [moduleH0Equiv_naturality]
      simpa only [x, LinearEquiv.apply_symm_apply] using hz n
    exact ((moduleH0Equiv M).apply_symm_apply z).symm.trans (congrArg (moduleH0Equiv M) he)

/-- Graded H1 vanishing makes every finite quotient projection surjective on H0. -/
theorem projection_h0_surjective_of_graded_vanishing :
    let _ := Chow.source_isNoetherian f
    (∀ k, Subsingleton (ModuleH (graded ((baseIdeal R J).comap f) M k) 1)) →
    ∀ n, Function.Surjective (moduleHMap (projection ((baseIdeal R J).comap f) M n) 0) := by
  let _ := Chow.source_isNoetherian f
  exact projection_h0_surjective_of_reconstruction (baseCohomologyScalars f)
    ((baseIdeal R J).comap f) M (cohomologyRestriction_bijective f J M 0).2

/-- The resulting lifts are actual global sections, with the specified quotient image. -/
theorem projection_sections_surjective_of_graded_vanishing :
    let _ := Chow.source_isNoetherian f
    (∀ k, Subsingleton (ModuleH (graded ((baseIdeal R J).comap f) M k) 1)) →
    ∀ n, Function.Surjective ((projection ((baseIdeal R J).comap f) M n).app ⊤) := by
  let _ := Chow.source_isNoetherian f
  dsimp only
  intro h n s
  obtain ⟨x, hx⟩ := projection_h0_surjective_of_graded_vanishing f J M h n
    ((moduleH0Equiv (quotient ((baseIdeal R J).comap f) M n)).symm s)
  refine ⟨moduleH0Equiv M x, ?_⟩
  rw [← moduleH0Equiv_naturality, hx]
  exact (moduleH0Equiv (quotient ((baseIdeal R J).comap f) M n)).apply_symm_apply s

end FLT.Mazur.BaseAdicCohomology
