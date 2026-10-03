/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RingEqualizerLocalization
public import Mathlib.AlgebraicGeometry.Pullbacks
/-!
# Scheme descent on localized ring equalizers

The normalization square is cartesian. Maps to affine targets descend uniquely;
maps to arbitrary targets descend wherever the normalized neighborhood maps
into one affine target open. The endpoint base is localized as well.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.RingEqualizerLocalDescent
open RingEqualizerLocalization
variable {C D : Type u} [CommRing C] [CommRing D] (f g : C →+* D) (s : f.eqLocus g)
/-- The localized normalization map. -/
def branch : Spec (.of (Localization.Away s.val)) ⟶ Spec (.of (E f g s)) :=
  Spec.map (CommRingCat.ofHom (E f g s).subtype)
/-- The first endpoint over the localized base. -/
def originFirst : Spec (.of (Localization.Away (f s.val))) ⟶
    Spec (.of (Localization.Away s.val)) := Spec.map (CommRingCat.ofHom (evalFirst f g s))
/-- The second endpoint over the localized base. -/
def originSecond : Spec (.of (Localization.Away (f s.val))) ⟶
    Spec (.of (Localization.Away s.val)) := Spec.map (CommRingCat.ofHom (evalSecond f g s))
/-- The principal open in the original equalizer spectrum. -/
def neighborhood : Spec (.of (E f g s)) ⟶ Spec (.of (f.eqLocus g)) :=
  Spec.map (CommRingCat.ofHom (restriction f g s))
/-- The corresponding principal open in the normalization. -/
def branchOpen : Spec (.of (Localization.Away s.val)) ⟶ Spec (.of C) :=
  Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away s.val)))
instance : IsOpenImmersion (neighborhood f g s) := IsOpenImmersion.of_isLocalization s
instance : IsOpenImmersion (branchOpen f g s) := IsOpenImmersion.of_isLocalization s.val
@[reassoc (attr := simp)] theorem branch_neighborhood :
    branch f g s ≫ neighborhood f g s =
      branchOpen f g s ≫ Spec.map (CommRingCat.ofHom (f.eqLocus g).subtype) := by
  rw [branch, neighborhood, branchOpen, ← Spec.map_comp, ← Spec.map_comp]
  rfl
@[reassoc (attr := simp)] theorem originFirst_branchOpen :
    originFirst f g s ≫ branchOpen f g s =
      Spec.map (CommRingCat.ofHom (algebraMap D (Localization.Away (f s.val)))) ≫
        Spec.map (CommRingCat.ofHom f) := by
  rw [originFirst, branchOpen, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext (evalFirst_algebraMap f g s)))
@[reassoc (attr := simp)] theorem originSecond_branchOpen :
    originSecond f g s ≫ branchOpen f g s =
      Spec.map (CommRingCat.ofHom (algebraMap D (Localization.Away (f s.val)))) ≫
        Spec.map (CommRingCat.ofHom g) := by
  rw [originSecond, branchOpen, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext (evalSecond_algebraMap f g s)))
theorem range_neighborhood : Set.range (neighborhood f g s) =
    (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum (f.eqLocus g))) :=
  PrimeSpectrum.localization_away_comap_range (E f g s) s
theorem range_branchOpen : Set.range (branchOpen f g s) =
    (PrimeSpectrum.basicOpen s.val : Set (PrimeSpectrum C)) :=
  PrimeSpectrum.localization_away_comap_range (Localization.Away s.val) s.val

/-- Unique descent to an affine spectrum. -/
theorem desc_spec {T : CommRingCat.{u}}
    (h : Spec (.of (Localization.Away s.val)) ⟶ Spec T)
    (w : originFirst f g s ≫ h = originSecond f g s ≫ h) :
    ∃! d : Spec (.of (E f g s)) ⟶ Spec T, branch f g s ≫ d = h := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective h
  have hw : (evalFirst f g s).comp φ.hom = (evalSecond f g s).comp φ.hom := by
    rw [originFirst, originSecond, ← Spec.map_comp, ← Spec.map_comp] at w
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective w)
  let δ : T →+* E f g s := φ.hom.codRestrict (E f g s) (fun r ↦ RingHom.congr_fun hw r)
  refine ⟨Spec.map (CommRingCat.ofHom δ), ?_, ?_⟩
  · dsimp only
    rw [branch, ← Spec.map_comp]; rfl
  · intro d hd
    obtain ⟨ε, rfl⟩ := Spec.map_surjective d
    rw [branch, ← Spec.map_comp] at hd
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun r ↦ Subtype.ext
      (congrArg (fun k ↦ k.hom r) (Spec.map_injective hd)))

/-- Unique descent to any affine scheme. -/
theorem desc_affine {Y : Scheme.{u}} [IsAffine Y]
    (h : Spec (.of (Localization.Away s.val)) ⟶ Y)
    (w : originFirst f g s ≫ h = originSecond f g s ≫ h) :
    ∃! d : Spec (.of (E f g s)) ⟶ Y, branch f g s ≫ d = h := by
  obtain ⟨d, hd, hu⟩ := desc_spec f g s (h ≫ Y.isoSpec.hom)
    (by simpa only [← Category.assoc] using congrArg (fun t ↦ t ≫ Y.isoSpec.hom) w)
  refine ⟨d ≫ Y.isoSpec.inv, ?_, ?_⟩
  · dsimp only
    rw [← Category.assoc, hd, Category.assoc, Y.isoSpec.hom_inv_id, Category.comp_id]
  · intro e he
    apply (cancel_mono Y.isoSpec.hom).mp
    simpa using hu (e ≫ Y.isoSpec.hom) (by dsimp only; rw [← Category.assoc, he])

/-- Descent on a neighborhood mapping into one affine target open. -/
theorem desc_on_open {Y : Scheme.{u}} (h : Spec (.of C) ⟶ Y)
    (w : Spec.map (CommRingCat.ofHom f) ≫ h = Spec.map (CommRingCat.ofHom g) ≫ h)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (hsU : PrimeSpectrum.basicOpen s.val ≤ h ⁻¹ᵁ U) :
    ∃ d : Spec (.of (E f g s)) ⟶ Y, branch f g s ≫ d = branchOpen f g s ≫ h := by
  have hr : Set.range (branchOpen f g s ≫ h) ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hsU
    have hz : branchOpen f g s z ∈ Set.range (branchOpen f g s) := ⟨z, rfl⟩
    rw [range_branchOpen] at hz
    exact hz
  let h' := IsOpenImmersion.lift U.ι (branchOpen f g s ≫ h) hr
  have w' : originFirst f g s ≫ h' = originSecond f g s ≫ h' := by
    apply (cancel_mono U.ι).mp
    simp only [Category.assoc, h', IsOpenImmersion.lift_fac,
      originFirst_branchOpen_assoc, originSecond_branchOpen_assoc, w]
  let : IsAffine U := hU
  obtain ⟨d, hd, _⟩ := desc_affine f g s h' w'
  refine ⟨d ≫ U.ι, ?_⟩
  rw [← Category.assoc, hd]
  exact IsOpenImmersion.lift_fac _ _ _

/-- Localizing the equalizer gives the normalization pullback square. -/
theorem isPullback : IsPullback (branchOpen f g s) (branch f g s)
    (Spec.map (CommRingCat.ofHom (f.eqLocus g).subtype)) (neighborhood f g s) := by
  let : IsLocalization ((Submonoid.powers s).map (f.eqLocus g).subtype)
      (Localization.Away s.val) := by
    rw [Submonoid.map_powers]
    exact inferInstanceAs (IsLocalization.Away s.val (Localization.Away s.val))
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (f.eqLocus g).subtype
      (E f g s).subtype (by rfl) (Submonoid.powers s))
end FLT.Mazur.RingEqualizerLocalDescent
