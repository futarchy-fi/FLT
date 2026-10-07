/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedLocalization
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The original graded ring restrictions are ring localizations

The full graded ring on a principal affine-base subopen is the localization
of the original graded ring at the degree-zero image of the base scalar.
The ring map is exactly the original restriction, including multiplication.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.AffinePieceSectionLocalization

universe u

namespace FLT.Mazur.IdealAdicGradedSections

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
variable {R : CommRingCat.{u}} (g : X ⟶ Spec R)

/-- The degree-zero image of the actual base scalar on an arbitrary open. -/
def baseTotalScalar (U : X.Opens) : R →+* Sections I U :=
  (algebraMap Γ(X, U) (Sections I U)).comp
    ((X.presheaf.map U.leTop.op).hom.comp (affineBaseScalars g))

/-- The direct-sum scalar action is multiplication by the actual degree-zero scalar. -/
lemma baseTotal_smul (U : X.Opens) (r : R) (s : baseTotal I g U) :
    r • s = @Mul.mul (Sections I U) inferInstance (baseTotalScalar I g U r) s := by
  change Sections I U at s
  change (X.presheaf.map U.leTop.op (affineBaseScalars g r)) • (s : Sections I U) = _
  exact Algebra.smul_def _ s

/-- The original graded restriction retains the same base scalars. -/
lemma baseTotalScalar_restrict {U V : X.Opens} (i : U ⟶ V) (r : R) :
    restrictRingHom I U i (baseTotalScalar I g V r) = baseTotalScalar I g U r := by
  change restrict I U i (of I V 0 (scalar I V
    (X.presheaf.map V.leTop.op (affineBaseScalars g r)))) =
      of I U 0 (scalar I U (X.presheaf.map U.leTop.op (affineBaseScalars g r)))
  rw [restrict_of, scalar_restrict]
  congr 2
  rw [← Functor.map_comp_apply]
  rfl

/-- On a principal subopen, the original scalar becomes a unit in the actual graded ring. -/
lemma baseTotalScalar_isUnit (V : X.affineOpens) (r : R) :
    IsUnit (baseTotalScalar I g (V.1 ⊓ g ⁻¹ᵁ PrimeSpectrum.basicOpen r) r) := by
  let _ := baseTotalRestriction_isLocalized I g V r
  have h := (Module.End.isUnit_iff _).mp (IsLocalizedModule.Away.isUnit_algebraMap
    (baseTotalRestriction I g (homOfLE (show V.1 ⊓ g ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ V.1
      from inf_le_left))) r)
  obtain ⟨s, hs⟩ := h.surjective (1 : Sections I (V.1 ⊓ g ⁻¹ᵁ PrimeSpectrum.basicOpen r))
  apply isUnit_iff_exists_inv.mpr
  refine ⟨s, ?_⟩
  exact (baseTotal_smul I g _ r s).symm.trans hs

/-- The actual principal graded-ring restriction is localization at the base scalar. -/
lemma gradedRestriction_isLocalization (V : X.affineOpens) (r : R) :
    let W := V.1 ⊓ g ⁻¹ᵁ PrimeSpectrum.basicOpen r
    let := (restrictRingHom I W (homOfLE inf_le_left)).toAlgebra
    IsLocalization.Away (baseTotalScalar I g V.1 r) (Sections I W) := by
  let W := V.1 ⊓ g ⁻¹ᵁ PrimeSpectrum.basicOpen r
  let i : W ⟶ V.1 := homOfLE inf_le_left
  let := (restrictRingHom I W i).toAlgebra
  let _ := baseTotalRestriction_isLocalized I g V r
  apply IsLocalization.Away.mk
  · change IsUnit (restrictRingHom I W i (baseTotalScalar I g V.1 r))
    rw [baseTotalScalar_restrict]
    exact baseTotalScalar_isUnit I g V r
  · intro s
    obtain ⟨n, t, ht⟩ := baseTotal_exists_numerator I g V r s
    refine ⟨n, t, ?_⟩
    change s * restrictRingHom I W i (baseTotalScalar I g V.1 r) ^ n =
      restrictRingHom I W i t
    rw [baseTotalScalar_restrict, _root_.mul_comm, ← map_pow]
    exact (baseTotal_smul I g W (r ^ n) s).symm.trans ht
  · intro s t hst
    have h : baseTotalRestriction I g i s = baseTotalRestriction I g i t := by
      rw [baseTotalRestriction_apply, baseTotalRestriction_apply]
      exact hst
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq r h
    refine ⟨n, ?_⟩
    rw [← map_pow]
    exact (baseTotal_smul I g V.1 (r ^ n) s).symm.trans
      (hn.trans (baseTotal_smul I g V.1 (r ^ n) t))

end FLT.Mazur.IdealAdicGradedSections
