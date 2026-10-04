/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionRatioBasicOpen

/-!
# Scalar multiples of generating sections

Multiplying a section by a function intersects its generator open with the
basic open of that function. The calculation uses the actual section ratio
and works over nonreduced rings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}} (M : X.Modules) (s t : Γ(M, ⊤))

/-- Ratios respect multiplication of the numerator by a global function. -/
lemma sectionRatioOn_smul_global (U : X.Opens) (hs : U ≤ sectionGeneratorOpen M s)
    (r : Γ(X, ⊤)) : sectionRatioOn M s U hs (r • t) =
      X.presheaf.map U.leTop.op r * sectionRatioOn M s U hs t := by
  apply (sectionRatioOn_eq_iff _ _ _ _ _ _).mpr
  rw [mul_smul, sectionRatioOn_smul]
  exact (M.map_smul U.leTop r t).symm

/-- A scalar multiple generates precisely where its scalar and section both generate. -/
lemma sectionGeneratorOpen_smul (r : Γ(X, ⊤)) :
    sectionGeneratorOpen M (r • s) = X.basicOpen r ⊓ sectionGeneratorOpen M s := by
  apply le_antisymm
  · let U := sectionGeneratorOpen M (r • s)
    have hmul : X.presheaf.map U.leTop.op r * sectionRatioOn M (r • s) U le_rfl s = 1 := by
      rw [← sectionRatioOn_smul_global, sectionRatioOn_self]
    have hr : IsUnit (X.presheaf.map U.leTop.op r) := isUnit_iff_exists_inv.mpr ⟨_, hmul⟩
    have hs : IsUnit (sectionRatioOn M (r • s) U le_rfl s) :=
      isUnit_iff_exists_inv.mpr ⟨_, (mul_comm _ _).trans hmul⟩
    refine le_inf ?_ (le_sectionGeneratorOpen_of_ratio_isUnit M (r • s) s U le_rfl hs)
    have h := X.basicOpen_of_isUnit hr
    rw [X.basicOpen_res] at h
    exact inf_eq_left.mp h
  · let U := sectionGeneratorOpen M s
    have hr : sectionRatioOn M s U le_rfl (r • s) = X.presheaf.map U.leTop.op r := by
      rw [sectionRatioOn_smul_global, sectionRatioOn_self, mul_one]
    have h := sectionRatioOn_basicOpen M s (r • s) U le_rfl
    rw [hr, X.basicOpen_res] at h
    exact (inf_comm _ _).le.trans (h.le.trans inf_le_right)

end FLT.Mazur.FCurve
