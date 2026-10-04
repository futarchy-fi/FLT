/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleHomIsomorphismOpen
public import FLT.Mazur.ModuleSectionRatios

/-!
# Ratios on the actual nonvanishing opens

The inverse section morphism gives a regular ratio on every subopen of the
canonical generator open. Restriction compatibility follows from naturality,
and the change-of-denominator identity holds on every common subopen.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤))

/-- The actual section map is invertible on sections of any subopen of its generator open. -/
lemma sectionGeneratorOpen_app_isIso (U : X.Opens) (hU : U ≤ sectionGeneratorOpen M s) :
    IsIso ((globalSectionHom M s).app U) :=
  ModuleSheafOpenIsoDetection.isIso_app_of_restrict _
    (moduleHomIsoOpen (globalSectionHom M s)) U hU

/-- A regular ratio on a subopen of the denominator's actual nonvanishing open. -/
def sectionRatioOn (U : X.Opens) (hU : U ≤ sectionGeneratorOpen M s)
    (t : Γ(M, ⊤)) : Γ(X, U) :=
  letI := sectionGeneratorOpen_app_isIso M s U hU
  (inv ((globalSectionHom M s).app U)) (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op t)

/-- The defining multiplication equation holds in the actual section module. -/
lemma sectionRatioOn_smul (U : X.Opens) (hU : U ≤ sectionGeneratorOpen M s)
    (t : Γ(M, ⊤)) :
    sectionRatioOn M s U hU t • M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s =
      M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op t := by
  let := sectionGeneratorOpen_app_isIso M s U hU
  exact ConcreteCategory.congr_hom (IsIso.inv_hom_id ((globalSectionHom M s).app U)) _

/-- Multiplication by the generator uniquely characterizes the local ratio. -/
lemma sectionRatioOn_eq_iff (U : X.Opens) (hU : U ≤ sectionGeneratorOpen M s)
    (t : Γ(M, ⊤)) (r : Γ(X, U)) :
    sectionRatioOn M s U hU t = r ↔
      r • M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s =
        M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op t := by
  let := sectionGeneratorOpen_app_isIso M s U hU
  constructor
  · intro hr
    rw [← hr, sectionRatioOn_smul]
  · intro hr
    apply (ConcreteCategory.bijective_of_isIso ((globalSectionHom M s).app U)).injective
    exact (sectionRatioOn_smul M s U hU t).trans hr.symm

/-- The section divided by itself is one on every subopen of its nonvanishing open. -/
@[simp] lemma sectionRatioOn_self (U : X.Opens) (hU : U ≤ sectionGeneratorOpen M s) :
    sectionRatioOn M s U hU s = 1 :=
  (sectionRatioOn_eq_iff M s U hU s 1).mpr (one_smul _ _)

/-- The local ratios commute with actual structure-sheaf restriction. -/
lemma sectionRatioOn_restrict (U V : X.Opens) (hU : U ≤ sectionGeneratorOpen M s)
    (hVU : V ≤ U) (t : Γ(M, ⊤)) :
    X.presheaf.map (homOfLE hVU).op (sectionRatioOn M s U hU t) =
      sectionRatioOn M s V (hVU.trans hU) t := by
  symm
  apply (sectionRatioOn_eq_iff _ _ _ _ _ _).mpr
  have he := congrArg (M.presheaf.map (homOfLE hVU).op) (sectionRatioOn_smul M s U hU t)
  erw [M.val.map_smul] at he
  change X.presheaf.map (homOfLE hVU).op (sectionRatioOn M s U hU t) •
    M.presheaf.map (homOfLE hVU).op
      (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s) = _ at he
  simpa only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using he

/-- Actual ratios obey the change-of-denominator identity on every common subopen. -/
lemma sectionRatioOn_change (t v : Γ(M, ⊤)) (U : X.Opens)
    (hs : U ≤ sectionGeneratorOpen M s) (ht : U ≤ sectionGeneratorOpen M t) :
    sectionRatioOn M s U hs t * sectionRatioOn M t U ht v = sectionRatioOn M s U hs v := by
  symm
  apply (sectionRatioOn_eq_iff _ _ _ _ _ _).mpr
  rw [mul_comm, mul_smul, sectionRatioOn_smul, sectionRatioOn_smul]

/-- Every transition ratio on a common nonvanishing open is a unit. -/
lemma sectionRatioOn_isUnit (t : Γ(M, ⊤)) (U : X.Opens)
    (hs : U ≤ sectionGeneratorOpen M s) (ht : U ≤ sectionGeneratorOpen M t) :
    IsUnit (sectionRatioOn M s U hs t) := by
  apply IsUnit.of_mul_eq_one (sectionRatioOn M t U ht s)
  rw [sectionRatioOn_change, sectionRatioOn_self]

end FLT.Mazur.FCurve
