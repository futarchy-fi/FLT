/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionRatios

/-!
# Pullback compatibility of section ratios

Ratios are characterized by multiplication with their actual generating section.
This characterization proves compatibility with arbitrary scheme pullback and
with sheaf isomorphisms, without unfolding the pullback adjunction.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤))
    [IsIso (globalSectionHom M s)]

/-- A regular function is the ratio precisely when multiplication recovers the numerator. -/
lemma sectionRatio_eq_iff (t : Γ(M, ⊤)) (r : Γ(X, ⊤)) :
    sectionRatio M s t = r ↔ r • s = t := by
  constructor
  · intro h
    rw [← h, sectionRatio_smul]
  · intro h
    rw [← h, sectionRatio_smul_numerator, sectionRatio_self, mul_one]

/-- Pullback carries a global generator to a global generator. -/
lemma globalSectionHom_isIso_pullGlobal {Y : Scheme.{u}} (f : Y ⟶ X) :
    IsIso (globalSectionHom ((pullback f).obj M) (pullGlobal f M s)) := by
  rw [globalSectionHom_pullGlobal]
  infer_instance

/-- Ratios commute with actual pullback along every scheme morphism. -/
lemma sectionRatio_pullGlobal {Y : Scheme.{u}} (f : Y ⟶ X) (t : Γ(M, ⊤)) :
    let := globalSectionHom_isIso_pullGlobal M s f
    sectionRatio ((pullback f).obj M) (pullGlobal f M s) (pullGlobal f M t) =
      f.appTop (sectionRatio M s t) := by
  let := globalSectionHom_isIso_pullGlobal M s f
  apply (sectionRatio_eq_iff _ _ _ _).mpr
  rw [← map_smulₛₗ, sectionRatio_smul]

/-- Sheaf comparisons preserve the ratios of the actual compared sections. -/
lemma sectionRatio_iso {N : X.Modules} (e : M ≅ N) (t : Γ(M, ⊤)) :
    let := globalSectionHom_isIso_transport M e s
    sectionRatio N (e.hom.app ⊤ s) (e.hom.app ⊤ t) = sectionRatio M s t := by
  let := globalSectionHom_isIso_transport M e s
  apply (sectionRatio_eq_iff _ _ _ _).mpr
  rw [← Hom.app_smul, sectionRatio_smul]

/-- Pullback of the ratio polynomial map is the polynomial map of pulled-back sections. -/
lemma sectionRatioRingMap_pullGlobal {Y : Scheme.{u}} (f : Y ⟶ X)
    {R : Type u} [CommRing R] (r : R →+* Γ(X, ⊤))
    {ι : Type u} (t : ι → Γ(M, ⊤)) :
    let := globalSectionHom_isIso_pullGlobal M s f
    sectionRatioRingMap ((pullback f).obj M) (pullGlobal f M s)
      (f.appTop.hom.comp r) (fun i ↦ pullGlobal f M (t i)) =
      f.appTop.hom.comp (sectionRatioRingMap M s r t) := by
  let := globalSectionHom_isIso_pullGlobal M s f
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [sectionRatioRingMap]
  · intro i
    simpa only [sectionRatioRingMap, MvPolynomial.eval₂Hom_X', RingHom.comp_apply,
      Function.comp_apply] using sectionRatio_pullGlobal M s f (t i)

end FLT.Mazur.FCurve
