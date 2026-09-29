/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalSubmoduleSectionLocalization

/-!
# Compatibility of constructed principal section images

Contracting either chart image and localizing at the product recovers the actual
image on the overlap, in one fixed ambient localization.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open CategoryTheory AlgebraicGeometry Opposite PrimeSpectrum
open Scheme.Modules
open FLT.Mazur.PrincipalSubmoduleCoordinates
open FLT.Mazur.PrincipalSubmoduleSectionLocalization
open FLT.Mazur.AffineCoherentSubmoduleExtension

universe u

namespace FLT.Mazur.PrincipalSubmoduleOverlap

variable {R : CommRingCat.{u}} {M : (Spec R).Modules} [M.IsQuasicoherent]
  {U : (Spec R).Opens} {L : U.toScheme.Modules}
  (i : L ⟶ M.restrict U.ι) (f g : R) (hf : basicOpen f ≤ U)

/-- Sections on an affine chart carry its coordinate-ring action. -/
local instance chartModule (N : (Spec (CommRingCat.of (Localization.Away f))).Modules)
    (V : (Spec (CommRingCat.of (Localization.Away f))).Opens) :
    Module (Localization.Away f) Γ(N, V) :=
  inferInstanceAs (Module (Localization.Away f)
    (((modulesSpecToSheaf (R := CommRingCat.of (Localization.Away f))).obj N).obj.obj (op V)))

omit [M.IsQuasicoherent] in
/-- The transported overlap action is the ambient base-ring action under inclusion. -/
lemma overlap_inclusion_smul (r : R) (y : overlapSections f g hf L) :
    inclusionSection i (f * g) ((basicOpen_mul_le_left f g).trans hf) (r • y) =
      r • inclusionSection i (f * g) ((basicOpen_mul_le_left f g).trans hf) y := by
  let V := basicOpen (algebraMap R (Localization.Away f) g)
  let x := (overlapIso f g hf L).inv y
  have he (z : Γ(L.restrict (chart U f hf), V)) :
      inclusionSection i (f * g) ((basicOpen_mul_le_left f g).trans hf)
          ((overlapIso f g hf L).hom z) =
        M.presheaf.map (eqToHom (by
          rw [← chart_image U (f * g) ((basicOpen_mul_le_left f g).trans hf),
            ← chart_basicOpen_image U f g hf, ← Scheme.Hom.comp_image]
          simp only [chart_comp]
          rfl)).op
          ((M.restrictAppIso (principalMap f) V).hom ((chartInclusion i f hf).app V z)) := by
    change M.presheaf.map _ (i.app _ (L.presheaf.map _ z)) =
      M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ (i.app _ z)))
    have hn := congrArg (fun a ↦ a.hom z) (i.mapPresheaf.naturality
      (eqToHom (chart_basicOpen_image U f g hf).symm).op)
    change i.app _ (L.presheaf.map _ z) = M.presheaf.map _ (i.app _ z) at hn
    apply (congrArg (fun t ↦ M.presheaf.map
      (eqToHom (chart_image U (f * g) ((basicOpen_mul_le_left f g).trans hf)).symm).op t)
      hn).trans
    simp only [← M.presheaf.map_comp_apply]
    exact (M.presheaf.map_comp_apply
      ((Scheme.Hom.opensFunctor U.ι).op.map (eqToHom (chart_basicOpen_image U f g hf).symm).op)
      (eqToHom (chart_image U (f * g) ((basicOpen_mul_le_left f g).trans hf)).symm).op
      (i.app _ z)).symm
  change inclusionSection i (f * g) _
    ((overlapIso f g hf L).hom (algebraMap R (Localization.Away f) r • x)) = _
  rw [he]
  have hs := ((modulesSpecToSheaf.map (chartInclusion i f hf)).hom.app (op V)).hom.map_smul
    (algebraMap R (Localization.Away f) r) x
  change (chartInclusion i f hf).app V (_ • x) = _ at hs
  rw [hs]
  apply (congrArg (fun t ↦ M.presheaf.map _ t)
    (AlgebraicGeometry.Scheme.Modules.restrictAppIso_smul_Spec (M := M)
      (CommRingCat.ofHom (algebraMap R (Localization.Away f))) r
      ((chartInclusion i f hf).app V x))).trans
  rw [M.map_smul_Spec, ← he, Iso.inv_hom_id_apply]

/-- A global numerator in the overlap image enters the first contraction after a power. -/
lemma overlap_numerator [L.IsQuasicoherent] (m : moduleSpecΓFunctor.obj M)
    (hm : LocalizedModule.mkLinearMap (.powers (f * g)) _ m ∈
      sectionSubmodule i (f * g) ((basicOpen_mul_le_left f g).trans hf)) :
    ∃ n : ℕ, g ^ n • m ∈ principalContraction f (sectionSubmodule i f hf) := by
  obtain ⟨y, hy⟩ := (mem_sectionSubmodule_iff_actual i _ _ _).mp hm
  obtain ⟨n, x, hx⟩ := exists_denominator f g hf L y
  let z := coordinates M f (inclusionSection i f hf x)
  have hz : z ∈ sectionSubmodule i f hf :=
    (mem_sectionSubmodule_iff_actual i f hf z).mpr ⟨x, rfl⟩
  obtain ⟨⟨m', ⟨_, a, rfl⟩⟩, ha⟩ := IsLocalizedModule.surj (.powers f)
    (LocalizedModule.mkLinearMap (.powers f) (moduleSpecΓFunctor.obj M)) z
  change f ^ a • z = LocalizedModule.mk m' 1 at ha
  have hm' : m' ∈ principalContraction f (sectionSubmodule i f hf) := by
    change LocalizedModule.mk m' 1 ∈ sectionSubmodule i f hf
    rw [← ha, ← algebraMap_smul (Localization.Away f)]
    exact (sectionSubmodule i f hf).smul_mem _ hz
  have hr : TildePrincipalOpen.localizationRestriction (moduleSpecΓFunctor.obj M) f g z =
      g ^ n • LocalizedModule.mk m 1 := by
    rw [← inclusionSection_coordinates_restriction i f g hf x, hx,
      overlap_inclusion_smul, LinearMapClass.map_smul_of_tower, hy]
    rfl
  have he := congrArg
    (TildePrincipalOpen.localizationRestriction (moduleSpecΓFunctor.obj M) f g) ha
  rw [_root_.map_smul, hr, TildePrincipalOpen.localizationRestriction_mk] at he
  have he' : LocalizedModule.mkLinearMap (.powers (f * g)) (moduleSpecΓFunctor.obj M)
      ((f ^ a * g ^ n) • m) = LocalizedModule.mkLinearMap (.powers (f * g)) _ m' := by
    simpa only [_root_.map_smul, mul_smul, LocalizedModule.mkLinearMap_apply] using he
  have hzero : LocalizedModule.mkLinearMap (.powers (f * g)) (moduleSpecΓFunctor.obj M)
      ((f ^ a * g ^ n) • m - m') = 0 := by rw [map_sub, he', sub_self]
  obtain ⟨⟨_, b, rfl⟩, hb⟩ := (IsLocalizedModule.eq_zero_iff (.powers (f * g))
    (LocalizedModule.mkLinearMap (.powers (f * g)) (moduleSpecΓFunctor.obj M))).mp hzero
  simp only [Submonoid.smul_def, smul_sub, sub_eq_zero] at hb
  have hp := (principalContraction f (sectionSubmodule i f hf)).smul_mem
    ((f * g) ^ b) hm'
  rw [← hb] at hp
  refine ⟨b + n, (principalContraction_pow_mem_iff f (sectionSubmodule i f hf)
    (b + a) _).mp ?_⟩
  convert hp using 1
  simp only [← mul_smul, mul_pow, pow_add]
  congr 1
  ring

/-- Contracting the first image and localizing at the product gives the overlap image. -/
theorem contraction_localized [L.IsQuasicoherent] :
    (principalContraction f (sectionSubmodule i f hf)).localized (.powers (f * g)) =
      sectionSubmodule i (f * g) ((basicOpen_mul_le_left f g).trans hf) := by
  apply le_antisymm
  · apply (Submodule.localized'gi (Localization.Away (f * g)) (.powers (f * g))
      (LocalizedModule.mkLinearMap (.powers (f * g)) (moduleSpecΓFunctor.obj M))).gc _ _ |>.mpr
    intro m hm
    obtain ⟨x, hx⟩ := (mem_sectionSubmodule_iff_actual i f hf _).mp hm
    apply (mem_sectionSubmodule_iff_actual i _ _ _).mpr
    refine ⟨L.presheaf.map (homOfLE (chart_product_le U f g hf)).op x, ?_⟩
    rw [inclusionSection_coordinates_restriction, hx]
    exact TildePrincipalOpen.localizationRestriction_mk _ f g m
  · rw [← principalContraction_localized (f * g)
      (sectionSubmodule i (f * g) ((basicOpen_mul_le_left f g).trans hf))]
    apply (Submodule.localized'gi (Localization.Away (f * g)) (.powers (f * g))
      (LocalizedModule.mkLinearMap (.powers (f * g)) (moduleSpecΓFunctor.obj M))).gc _ _ |>.mpr
    intro m hm
    obtain ⟨n, hn⟩ := overlap_numerator i f g hf m hm
    apply (numerator_mem_away_iff _ _ _).mpr
    exact ⟨n, by simpa only [mul_pow, mul_smul] using
      (principalContraction f (sectionSubmodule i f hf)).smul_mem (f ^ n) hn⟩

/-- Transport the product equality along an explicit equality of denominators. -/
lemma contraction_localized_of_eq [L.IsQuasicoherent] (p : R) (hp : f * g = p)
    (hpU : basicOpen p ≤ U) :
    (principalContraction f (sectionSubmodule i f hf)).localized (.powers p) =
      sectionSubmodule i p hpU := by
  subst p
  exact contraction_localized i f g hf

/-- The second contraction is compared in the same `f * g` ambient localization. -/
theorem contraction_localized_right [L.IsQuasicoherent] (hg : basicOpen g ≤ U) :
    (principalContraction g (sectionSubmodule i g hg)).localized (.powers (f * g)) =
      sectionSubmodule i (f * g) ((basicOpen_mul_le_left f g).trans hf) := by
  exact contraction_localized_of_eq i g f hg (f * g) (mul_comm g f)
    ((basicOpen_mul_le_left f g).trans hf)

/-- All constructed principal section images satisfy the ambient overlap condition. -/
theorem sectionSubmodule_compatible [L.IsQuasicoherent] {ι : Type*}
    (d : ι → R) (hd : ∀ k, basicOpen (d k) ≤ U) :
    Compatible d (fun k ↦ sectionSubmodule i (d k) (hd k)) := by
  intro j k
  exact (contraction_localized i (d j) (d k) (hd j)).trans
    (contraction_localized_right i (d j) (d k) (hd j) (hd k)).symm

end FLT.Mazur.PrincipalSubmoduleOverlap
