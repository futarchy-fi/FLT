/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicThickening

/-!
# Base thickenings as quotient spectra

The closed subscheme of the base ideal is Spec of the ring quotient.
Consequently the power-ideal thickening of X is the actual fibred product
with Spec(R / J^n), with its original immersion in X.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.BaseAdicThickening

variable (R : CommRingCat.{u}) (J : Ideal R)

/-- The quotient spectrum has precisely the specified base ideal as its kernel. -/
lemma quotientSpec_ker :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).ker = baseIdeal R J := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.Hom.ker_apply, baseIdeal_top]
  ext s
  change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop s = 0 ↔
    s ∈ J.map (Scheme.ΓSpecIso R).inv.hom
  rw [Ideal.mem_map_iff_of_surjective (Scheme.ΓSpecIso R).inv.hom
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.surjective]
  constructor
  · intro hs
    refine ⟨(Scheme.ΓSpecIso R).hom s, ?_, ?_⟩
    · apply Ideal.Quotient.eq_zero_iff_mem.mp
      have he := congrArg (fun k : Γ(Spec R, ⊤) ⟶ CommRingCat.of (R ⧸ J) ↦ k s)
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J)))
      change (Scheme.ΓSpecIso _).hom
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop s) =
          Ideal.Quotient.mk J ((Scheme.ΓSpecIso R).hom s) at he
      rw [show (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop s = 0 from hs,
        map_zero] at he
      exact he.symm
    · exact (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm_apply_apply s
  · rintro ⟨r, hr, rfl⟩
    apply (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective
    have he := congrArg (fun k : R ⟶ Γ(Spec (CommRingCat.of (R ⧸ J)), ⊤) ↦ k r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    change (Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk J r) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop
        ((Scheme.ΓSpecIso R).inv r) at he
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero] at he
    exact congrArg (fun s ↦ (Scheme.ΓSpecIso _).hom s) he.symm

/-- The quotient-spectrum comparison is over the original affine base. -/
def quotientSpecIso : Spec (CommRingCat.of (R ⧸ J)) ≅ (baseIdeal R J).subscheme :=
  asIso (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).toImage ≪≫
    subschemeCongr (quotientSpec_ker R J)

@[reassoc (attr := simp)]
lemma quotientSpecIso_hom_ι :
    (quotientSpecIso R J).hom ≫ (baseIdeal R J).subschemeι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
  simp [quotientSpecIso, Scheme.Hom.toImage_imageι]

/-- Identify the n-th base thickening with the spectrum of the n-th quotient. -/
def powerQuotientSpecIso (n : ℕ) :
    (baseIdeal R J ^ n).subscheme ≅ Spec (CommRingCat.of (R ⧸ J ^ n)) :=
  subschemeCongr (baseIdeal_pow R J n).symm ≪≫ (quotientSpecIso R (J ^ n)).symm

@[reassoc (attr := simp)]
lemma powerQuotientSpecIso_hom_map (n : ℕ) :
    (powerQuotientSpecIso R J n).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ n))) =
        (baseIdeal R J ^ n).subschemeι := by
  simp only [powerQuotientSpecIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← quotientSpecIso_hom_ι R (J ^ n), Iso.inv_hom_id_assoc]
  exact subschemeCongr_hom_ι _

/-- The actual base-changed quotient spectrum, retaining the power-ideal thickening. -/
def quotientPullbackIso {X : Scheme.{u}} (f : X ⟶ Spec R) (n : ℕ) :
    ((baseIdeal R J).comap f ^ n).subscheme ≅
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ n)))) :=
  powerPullbackIso (baseIdeal R J) f n ≪≫
    asIso (pullback.map f (baseIdeal R J ^ n).subschemeι
      f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ n))))
      (𝟙 X) (powerQuotientSpecIso R J n).hom (𝟙 _) (by simp) (by simp))

/-- The quotient-spectrum pullback comparison is over the original total space. -/
@[reassoc (attr := simp)]
lemma quotientPullbackIso_hom_fst {X : Scheme.{u}} (f : X ⟶ Spec R) (n : ℕ) :
    (quotientPullbackIso R J f n).hom ≫
      pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ n)))) =
        ((baseIdeal R J).comap f ^ n).subschemeι := by
  simp [quotientPullbackIso]

end FLT.Mazur.BaseAdicThickening
