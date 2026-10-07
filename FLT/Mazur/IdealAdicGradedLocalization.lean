/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DirectSumLocalization
public import FLT.Mazur.IdealAdicGradedRestriction
public import FLT.Mazur.AffinePieceSectionLocalization

/-!
# Localization of all actual graded coefficients at once

On an affine source open, restriction over a principal affine-base open is
localization for the full direct sum of the actual ideal-adic quotient sheaves.
The map is the original graded restriction, with its original base scalars.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.IdealAdicQuotient FLT.Mazur.AffinePieceSectionLocalization
open scoped DirectSum

universe u

namespace FLT.Mazur.IdealAdicGradedSections

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
variable {R : CommRingCat.{u}} (g : X ⟶ Spec R)

/-- Actual total coefficients with the scalar action induced by the specified affine base. -/
abbrev baseTotal (U : X.Opens) : ModuleCat R := ModuleCat.of R
  (⨁ n : ℕ, baseSections (idealGraded I n) (affineBaseScalars g) U)

/-- The full direct sum of actual quotient-sheaf restrictions. -/
def baseTotalRestriction {U V : X.Opens} (i : U ⟶ V) :
    baseTotal I g V →ₗ[R] baseTotal I g U :=
  DirectSum.lmap (fun n ↦ AffinePieceSectionLocalization.baseRestriction (idealGraded I n)
    (affineBaseScalars g) i.le)

/-- The base-linear restriction is the original graded-ring restriction on coefficients. -/
lemma baseTotalRestriction_apply {U V : X.Opens} (i : U ⟶ V) (s : Sections I V) :
    baseTotalRestriction I g i s = restrictRingHom I U i s := by
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add s t hs ht => simp only [map_add, hs, ht]
  | of n s =>
    exact (DirectSum.lmap_of (fun k ↦ AffinePieceSectionLocalization.baseRestriction
      (idealGraded I k) (affineBaseScalars g) i.le) n s).trans
        (restrict_of I U i n s).symm

/-- All coefficient degrees localize simultaneously on an affine source piece. -/
lemma baseTotalRestriction_isLocalized (V : X.affineOpens) (r : R) :
    IsLocalizedModule.Away r (baseTotalRestriction I g
      (homOfLE (show V.1 ⊓ g ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ V.1 from inf_le_left))) := by
  have (n : ℕ) := AffinePieceSectionLocalization.affinePiece_sectionRestriction_isLocalized
    (idealGraded I n) g V.1 V.2 r
  exact DirectSumLocalization.isLocalizedModule r _

/-- A finite-support graded section over a principal base open has one actual numerator. -/
lemma baseTotal_exists_numerator (V : X.affineOpens) (r : R)
    (s : baseTotal I g (V.1 ⊓ g ⁻¹ᵁ PrimeSpectrum.basicOpen r)) :
    ∃ (n : ℕ) (t : Sections I V.1),
      r ^ n • s = restrictRingHom I _ (homOfLE inf_le_left) t := by
  let _ := baseTotalRestriction_isLocalized I g V r
  obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj
    (baseTotalRestriction I g (homOfLE inf_le_left)) r s
  exact ⟨n, t, ht.trans (baseTotalRestriction_apply I g _ t)⟩

/-- Vanishing after principal restriction is killed by one power in every coefficient degree. -/
lemma baseTotal_exists_annihilator (V : X.affineOpens) (r : R)
    (s : baseTotal I g V.1)
    (hs : restrictRingHom I (V.1 ⊓ g ⁻¹ᵁ PrimeSpectrum.basicOpen r)
      (homOfLE inf_le_left) s = 0) : ∃ n : ℕ, r ^ n • s = 0 := by
  let _ := baseTotalRestriction_isLocalized I g V r
  have h : baseTotalRestriction I g
      (homOfLE (show V.1 ⊓ g ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ V.1 from inf_le_left)) s =
        baseTotalRestriction I g (homOfLE inf_le_left) 0 := by
    rw [baseTotalRestriction_apply, map_zero]
    exact hs
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq r h
  exact ⟨n, by simpa only [smul_zero] using hn⟩

end FLT.Mazur.IdealAdicGradedSections
