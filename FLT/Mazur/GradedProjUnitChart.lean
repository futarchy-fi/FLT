/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Maps into Proj from invertible homogeneous coordinates

A ring evaluation with a unit homogeneous denominator gives a scheme map
into its Proj chart. Multiplying the denominator by another invertible
homogeneous element does not change the resulting map into Proj.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
universe u
namespace FLT.Mazur.GradedProjUnitChart
variable {A : Type u} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}} (φ : A →+* Γ(X, ⊤))
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Evaluate a degree-zero homogeneous localization at a unit denominator. -/
def evaluation (f : A) (hf : IsUnit (φ f)) : Away 𝒜 f →+* Γ(X, ⊤) :=
  (IsLocalization.Away.lift (S := Localization.Away f) f hf).comp
    (algebraMap (Away 𝒜 f) (Localization.Away f))

/-- A localized fraction satisfies its numerator-denominator equation after evaluation. -/
lemma evaluation_mk_mul (f : A) (hf : IsUnit (φ f))
    (c : NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    evaluation 𝒜 φ f hf (HomogeneousLocalization.mk c) * φ c.den = φ c.num := by
  let ψ := IsLocalization.Away.lift (S := Localization.Away f) f hf
  change ψ (HomogeneousLocalization.mk c).val * φ c.den = _
  rw [← IsLocalization.Away.lift_eq (S := Localization.Away f) f hf c.den,
    ← IsLocalization.Away.lift_eq (S := Localization.Away f) f hf c.num, ← map_mul]
  congr 1
  simpa only [HomogeneousLocalization.val_mk, Localization.mk_eq_mk'] using
    IsLocalization.mk'_spec (Localization.Away f) (c.num : A) ⟨c.den, c.den_mem⟩

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- Every allowed denominator has invertible image under evaluation. -/
lemma denominator_isUnit (f : A) (hf : IsUnit (φ f))
    (c : NumDenSameDeg 𝒜 (Submonoid.powers f)) : IsUnit (φ c.den) := by
  obtain ⟨n, hn⟩ := c.den_mem
  rw [← hn, map_pow]
  exact hf.pow n

/-- The induced map to the affine homogeneous-localization chart. -/
def toAffine (f : A) (hf : IsUnit (φ f)) : X ⟶ Spec (.of (Away 𝒜 f)) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (evaluation 𝒜 φ f hf))

/-- The actual scheme morphism into Proj on an invertible positive-degree coordinate. -/
def toProj (f : A) (hf : IsUnit (φ f)) {d : ℕ} (hd : f ∈ 𝒜 d) (hpos : 0 < d) :
    X ⟶ Proj 𝒜 := toAffine 𝒜 φ f hf ≫ Proj.awayι 𝒜 f hd hpos

/-- Evaluation commutes with the standard Proj chart transition to a product denominator. -/
lemma evaluation_awayMap {f g : A} {n : ℕ} (hg : g ∈ 𝒜 n)
    (hf : IsUnit (φ f)) (hx : IsUnit (φ (f * g))) :
    (evaluation 𝒜 φ (f * g) hx).comp (awayMap 𝒜 hg rfl) = evaluation 𝒜 φ f hf := by
  have hunit : IsUnit (algebraMap A (Localization.Away (f * g)) f) :=
    isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right f g))
      (IsLocalization.Away.algebraMap_isUnit (f * g))
  have he :
      (IsLocalization.Away.lift (S := Localization.Away (f * g)) (f * g) hx).comp
        (Localization.awayLift (algebraMap A (Localization.Away (f * g))) f hunit) =
      IsLocalization.Away.lift (S := Localization.Away f) f hf := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers f)
    ext a
    simp only [RingHom.comp_apply, Localization.awayLift, IsLocalization.Away.lift_eq]
  ext a
  change IsLocalization.Away.lift (S := Localization.Away (f * g)) (f * g) hx
    (awayMap 𝒜 hg rfl a).val = _
  rw [val_awayMap]
  exact RingHom.congr_fun he a.val

/-- The affine chart maps commute with the standard transition morphism. -/
lemma toAffine_awayMap {f g : A} {n : ℕ} (hg : g ∈ 𝒜 n)
    (hf : IsUnit (φ f)) (hx : IsUnit (φ (f * g))) :
    toAffine 𝒜 φ (f * g) hx ≫ Spec.map (CommRingCat.ofHom (awayMap 𝒜 hg rfl)) =
      toAffine 𝒜 φ f hf := by
  simp only [toAffine, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [evaluation_awayMap]

/-- Refining an invertible coordinate by an invertible homogeneous factor preserves the Proj map. -/
lemma toProj_mul {f g : A} {d n : ℕ} (hd : f ∈ 𝒜 d) (hpos : 0 < d) (hg : g ∈ 𝒜 n)
    (hf : IsUnit (φ f)) (hx : IsUnit (φ (f * g))) :
    toProj 𝒜 φ (f * g) hx (SetLike.mul_mem_graded hd hg) (hpos.trans_le (d.le_add_right n)) =
      toProj 𝒜 φ f hf hd hpos := by
  unfold toProj
  rw [← Proj.SpecMap_awayMap_awayι 𝒜 hd hpos hg rfl,
    ← Category.assoc, toAffine_awayMap]

/-- Any two invertible positive-degree coordinates give the same map into Proj. -/
lemma toProj_eq {f g : A} {d n : ℕ} (hd : f ∈ 𝒜 d) (hpos : 0 < d)
    (hg : g ∈ 𝒜 n) (hn : 0 < n) (hf : IsUnit (φ f)) (hgu : IsUnit (φ g)) :
    toProj 𝒜 φ f hf hd hpos = toProj 𝒜 φ g hgu hg hn := by
  have hx : IsUnit (φ (f * g)) := by rw [map_mul]; exact hf.mul hgu
  have hy : IsUnit (φ (g * f)) := by rw [map_mul]; exact hgu.mul hf
  rw [← toProj_mul 𝒜 φ hd hpos hg hf hx]
  simpa only [mul_comm f g, Nat.add_comm d n] using toProj_mul 𝒜 φ hg hn hd hgu hy

/-- Homogeneous evaluation is natural in the target ring of functions. -/
lemma evaluation_comp {Y : Scheme.{u}} (ψ : Γ(X, ⊤) →+* Γ(Y, ⊤))
    (f : A) (hf : IsUnit (φ f)) :
    ψ.comp (evaluation 𝒜 φ f hf) = evaluation 𝒜 (ψ.comp φ) f (hf.map ψ) := by
  have he : ψ.comp (IsLocalization.Away.lift (S := Localization.Away f) f hf) =
      IsLocalization.Away.lift (S := Localization.Away f) (g := ψ.comp φ) f (hf.map ψ) := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers f)
    ext a
    simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq]
  exact congrArg (fun k ↦ k.comp (algebraMap (Away 𝒜 f) (Localization.Away f))) he

/-- The affine chart morphism commutes with pullback of regular functions. -/
lemma toAffine_naturality {Y : Scheme.{u}} (k : Y ⟶ X) (f : A) (hf : IsUnit (φ f)) :
    k ≫ toAffine 𝒜 φ f hf =
      toAffine 𝒜 (k.appTop.hom.comp φ) f (hf.map k.appTop.hom) := by
  simp only [toAffine, ← Category.assoc, Scheme.toSpecΓ_naturality]
  simp only [Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (evaluation_comp 𝒜 φ k.appTop.hom f hf)

/-- The map into Proj commutes with pullback of regular functions. -/
lemma toProj_naturality {Y : Scheme.{u}} (k : Y ⟶ X) (f : A) (hf : IsUnit (φ f))
    {d : ℕ} (hd : f ∈ 𝒜 d) (hpos : 0 < d) :
    k ≫ toProj 𝒜 φ f hf hd hpos =
      toProj 𝒜 (k.appTop.hom.comp φ) f (hf.map k.appTop.hom) hd hpos := by
  rw [toProj, ← Category.assoc, toAffine_naturality]
  rfl

end FLT.Mazur.GradedProjUnitChart
