/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierCharts
public import FLT.Mazur.FamilyTransport
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Algebra and flatness for relative Cartier pullback

The local algebra input to Stacks 056Q uses flatness of the quotient by the
regular equation. The base-change algebra itself need not be flat.
The geometric comparison identifies the pulled-back closed subscheme with the
base change of the original divisor and proves flatness over the new base.
Identity and composite comparisons retain the actual ideal sheaves.

The affine comparison between ideal-sheaf pullback and extension of ideals is
still needed to deduce the full `RelativeCartierBaseChange` contract.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

section Algebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- Multiplication by an equation followed by its quotient is exact over the base. -/
lemma exact_mul_quotient (h : B) :
    Function.Exact ((LinearMap.mul B B h).restrictScalars A)
      (Ideal.Quotient.mkₐ A (Ideal.span {h})).toLinearMap := by
  intro b
  change Ideal.Quotient.mk (Ideal.span {h}) b = 0 ↔ ∃ c, h * c = b
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact exists_congr fun c ↦ eq_comm

/-- A flat quotient preserves injectivity of multiplication after arbitrary tensoring. -/
lemma lTensor_mul_injective_of_quotient_flat (h : B) (hh : IsRegular h)
    [Module.Flat A (B ⧸ Ideal.span {h})]
    (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Injective (((LinearMap.mul B B h).restrictScalars A).lTensor M) := by
  apply LinearMap.lTensor_injective_of_exact_of_flat
    (Ideal.Quotient.mkₐ A (Ideal.span {h})).toLinearMap
    (Ideal.Quotient.mk_surjective) _ hh.left (exact_mul_quotient h)

/-- The C5 local input: `1 ⊗ h` is regular when `h` is regular with flat quotient. -/
theorem isRegular_one_tmul_of_quotient_flat (h : B) (hh : IsRegular h)
    [Module.Flat A (B ⧸ Ideal.span {h})]
    (A' : Type*) [CommRing A'] [Algebra A A'] :
    IsRegular (1 ⊗ₜ[A] h : A' ⊗[A] B) := by
  rw [← isLeftRegular_iff_isRegular]
  have he : (((LinearMap.mul B B h).restrictScalars A).lTensor A') =
      LinearMap.mul A (A' ⊗[A] B) (1 ⊗ₜ[A] h) := by
    ext a b
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  have hi := lTensor_mul_injective_of_quotient_flat (A := A) h hh A'
  rw [he] at hi
  exact hi

/-- The tensor sequence stays exact at the middle term without a flatness assumption. -/
lemma lTensor_exact_mul_quotient (h : B)
    (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Exact (((LinearMap.mul B B h).restrictScalars A).lTensor M)
      ((Ideal.Quotient.mkₐ A (Ideal.span {h})).toLinearMap.lTensor M) :=
  lTensor_exact M (exact_mul_quotient h) Ideal.Quotient.mk_surjective

/-- Extension of the principal ideal has the expected tensor equation. -/
lemma map_span_includeRight (h : B) (A' : Type*) [CommRing A'] [Algebra A A'] :
    (Ideal.span {h}).map
        (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B) =
      Ideal.span {(1 : A') ⊗ₜ[A] h} := by
  rw [Ideal.map_span, Set.image_singleton]
  rfl

/-- The kernel of the tensor quotient map is the pulled-back principal ideal. -/
lemma ker_tensor_quotient (h : B) (A' : Type*) [CommRing A'] [Algebra A A'] :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id A A')
        (Ideal.Quotient.mkₐ A (Ideal.span {h}))).toRingHom =
      Ideal.span {(1 : A') ⊗ₜ[A] h} := by
  have hk := Algebra.TensorProduct.lTensor_ker (A := A')
    (Ideal.Quotient.mkₐ A (Ideal.span {h})) Ideal.Quotient.mk_surjective
  change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id A A')
    (Ideal.Quotient.mkₐ A (Ideal.span {h}))) = _
  rw [hk]
  change (RingHom.ker (Ideal.Quotient.mk (Ideal.span {h}))).map _ = _
  rw [Ideal.mk_ker, map_span_includeRight]

/-- Quotient by the tensor equation is the base change of the original quotient. -/
def tensorPrincipalQuotientEquiv (h : B) (A' : Type*) [CommRing A'] [Algebra A A'] :
    A' ⊗[A] (B ⧸ Ideal.span {h}) ≃ₐ[A']
      (A' ⊗[A] B) ⧸ Ideal.span {(1 : A') ⊗ₜ[A] h} :=
  (Algebra.TensorProduct.tensorQuotientEquiv A' B A' (Ideal.span {h})).trans
    (Ideal.quotientEquivAlgOfEq A' (map_span_includeRight (A := A) h A'))

/-- The quotient comparison sends pure tensors to their residue classes. -/
@[simp]
lemma tensorPrincipalQuotientEquiv_tmul (h : B)
    (A' : Type*) [CommRing A'] [Algebra A A'] (a : A') (b : B) :
    tensorPrincipalQuotientEquiv h A' (a ⊗ₜ[A] Ideal.Quotient.mk (Ideal.span {h}) b) =
      Ideal.Quotient.mk (Ideal.span {(1 : A') ⊗ₜ[A] h}) (a ⊗ₜ[A] b) := by
  simp [tensorPrincipalQuotientEquiv]

/-- The inverse quotient comparison is the canonical tensor quotient map. -/
@[simp]
lemma tensorPrincipalQuotientEquiv_symm_mk (h : B)
    (A' : Type*) [CommRing A'] [Algebra A A'] (a : A') (b : B) :
    (tensorPrincipalQuotientEquiv (A := A) h A').symm
        (Ideal.Quotient.mk (Ideal.span {(1 : A') ⊗ₜ[A] h}) (a ⊗ₜ[A] b)) =
      a ⊗ₜ[A] Ideal.Quotient.mk (Ideal.span {h}) b := by
  apply (tensorPrincipalQuotientEquiv (A := A) h A').injective
  simp

/-- The pulled-back quotient remains flat over the new base algebra. -/
theorem flat_tensor_principal_quotient (h : B)
    [Module.Flat A (B ⧸ Ideal.span {h})]
    (A' : Type*) [CommRing A'] [Algebra A A'] :
    Module.Flat A' ((A' ⊗[A] B) ⧸ Ideal.span {(1 : A') ⊗ₜ[A] h}) :=
  Module.Flat.of_linearEquiv (tensorPrincipalQuotientEquiv (A := A) h A').symm.toLinearEquiv

/-- Both algebraic conditions of a relative equation survive arbitrary base change. -/
theorem relative_equation_baseChange (h : B) (hh : IsRegular h)
    [Module.Flat A (B ⧸ Ideal.span {h})]
    (A' : Type*) [CommRing A'] [Algebra A A'] :
    IsRegular (1 ⊗ₜ[A] h : A' ⊗[A] B) ∧
      Module.Flat A' ((A' ⊗[A] B) ⧸ Ideal.span {(1 : A') ⊗ₜ[A] h}) :=
  ⟨isRegular_one_tmul_of_quotient_flat h hh A', flat_tensor_principal_quotient h A'⟩

/-- Regular tensor equations transport through the ring comparison of an affine chart. -/
lemma isRegular_tensor_equation (h : B) (hh : IsRegular h)
    [Module.Flat A (B ⧸ Ideal.span {h})]
    (A' : Type*) [CommRing A'] [Algebra A A']
    {C : Type*} [CommRing C] (e : A' ⊗[A] B ≃+* C) :
    IsRegular (e (1 ⊗ₜ[A] h)) := by
  rw [← isLeftRegular_iff_isRegular]
  intro x y hxy
  apply e.symm.injective
  apply (isRegular_one_tmul_of_quotient_flat h hh A').left
  apply e.injective
  simpa only [map_mul, RingEquiv.apply_symm_apply] using hxy

/-- The other ordering of the tensor factors used by affine scheme pullbacks. -/
theorem isRegular_tmul_one_of_quotient_flat (h : B) (hh : IsRegular h)
    [Module.Flat A (B ⧸ Ideal.span {h})]
    (A' : Type*) [CommRing A'] [Algebra A A'] :
    IsRegular (h ⊗ₜ[A] 1 : B ⊗[A] A') :=
  isRegular_tensor_equation h hh A' (Algebra.TensorProduct.comm A A' B).toRingEquiv

end Algebra

section Geometry

variable {X S T U : Scheme.{u}}

/-- The inverse image of the divisor is its base change over the original base. -/
def divisorBaseChangeIso (f : X ⟶ S) (g : T ⟶ S) (I : X.IdealSheafData) :
    (I.comap (pullback.fst f g)).subscheme ≅ pullback (I.subschemeι ≫ f) g :=
  I.comapIso (pullback.fst f g) ≪≫
    pullbackSymmetry (pullback.fst f g) I.subschemeι ≪≫
      pullbackRightPullbackFstIso f g I.subschemeι

/-- The divisor comparison preserves the map to the new base. -/
@[reassoc (attr := simp)]
lemma divisorBaseChangeIso_hom_snd (f : X ⟶ S) (g : T ⟶ S)
    (I : X.IdealSheafData) :
    (divisorBaseChangeIso f g I).hom ≫ pullback.snd (I.subschemeι ≫ f) g =
      (I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g := by
  simp [divisorBaseChangeIso]

/-- The inverse comparison also preserves the map to the new base. -/
@[reassoc (attr := simp)]
lemma divisorBaseChangeIso_inv_subschemeι_snd (f : X ⟶ S) (g : T ⟶ S)
    (I : X.IdealSheafData) :
    (divisorBaseChangeIso f g I).inv ≫
        (I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g =
      pullback.snd (I.subschemeι ≫ f) g := by
  rw [← divisorBaseChangeIso_hom_snd, Iso.inv_hom_id_assoc]

/-- The comparison is compatible with the original divisor's closed immersion. -/
@[reassoc (attr := simp)]
lemma divisorBaseChangeIso_hom_fst_subschemeι (f : X ⟶ S) (g : T ⟶ S)
    (I : X.IdealSheafData) :
    (divisorBaseChangeIso f g I).hom ≫ pullback.fst (I.subschemeι ≫ f) g ≫
        I.subschemeι =
      (I.comap (pullback.fst f g)).subschemeι ≫ pullback.fst f g := by
  simp only [divisorBaseChangeIso, Iso.trans_hom, Category.assoc,
    pullbackRightPullbackFstIso_hom_fst_assoc,
    pullbackSymmetry_hom_comp_fst_assoc]
  rw [← pullback.condition, I.comapIso_hom_fst_assoc]

/-- The inverse comparison preserves the map to the original ambient scheme. -/
@[reassoc (attr := simp)]
lemma divisorBaseChangeIso_inv_subschemeι_fst (f : X ⟶ S) (g : T ⟶ S)
    (I : X.IdealSheafData) :
    (divisorBaseChangeIso f g I).inv ≫
        (I.comap (pullback.fst f g)).subschemeι ≫ pullback.fst f g =
      pullback.fst (I.subschemeι ≫ f) g ≫ I.subschemeι := by
  rw [← divisorBaseChangeIso_hom_fst_subschemeι, Iso.inv_hom_id_assoc]

/-- The divisor comparison is an isomorphism over the new base. -/
def divisorBaseChangeOverIso (f : X ⟶ S) (g : T ⟶ S) (I : X.IdealSheafData) :
    Over.mk ((I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g) ≅
      Over.mk (pullback.snd (I.subschemeι ≫ f) g) :=
  Over.isoMk (divisorBaseChangeIso f g I) (divisorBaseChangeIso_hom_snd f g I)

/-- Flatness of the divisor over the base survives arbitrary base change. -/
theorem flat_divisor_baseChange (f : X ⟶ S) (g : T ⟶ S) (I : X.IdealSheafData)
    [Flat (I.subschemeι ≫ f)] :
    Flat ((I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g) := by
  rw [← divisorBaseChangeIso_hom_snd]
  infer_instance

/-- The flat half of the relative Cartier condition has no Cartier hypothesis. -/
lemma RelativeEffectiveCartier.flat_baseChange {f : X ⟶ S} {I : X.IdealSheafData}
    (hI : RelativeEffectiveCartier f I) (g : T ⟶ S) :
    Flat ((I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g) := by
  let := hI.2
  exact flat_divisor_baseChange f g I

/-- Pullback of ideals along the identity family agrees with the original ideal. -/
lemma divisorPullback_id (f : X ⟶ S) (I : X.IdealSheafData) :
    (I.comap (pullback.fst f (𝟙 S))).comap
      (familyPullbackIdIso (Over.mk f)).inv.left = I := by
  have he : (familyPullbackIdIso (Over.mk f)).inv.left ≫
      pullback.fst f (𝟙 S) = 𝟙 X := familyPullbackIdIso_inv_left_fst (Over.mk f)
  rw [← Scheme.IdealSheafData.comap_comp, he]
  exact I.comap_id

/-- Iterating base change agrees with the composite comparison on actual ideal sheaves. -/
lemma divisorPullback_comp (f : X ⟶ S) (g : T ⟶ S) (h : U ⟶ T)
    (I : X.IdealSheafData) :
    (I.comap (pullback.fst f (h ≫ g))).comap
        (familyPullbackCompIso (Over.mk f) g h).hom.left =
      (I.comap (pullback.fst f g)).comap (pullback.fst (pullback.snd f g) h) := by
  have he : (familyPullbackCompIso (Over.mk f) g h).hom.left ≫
      pullback.fst f (h ≫ g) =
        pullback.fst (pullback.snd f g) h ≫ pullback.fst f g :=
    familyPullbackCompIso_hom_left_fst (Over.mk f) g h
  rw [← Scheme.IdealSheafData.comap_comp, he, Scheme.IdealSheafData.comap_comp]

/-- The inverse composite comparison transports the iterated ideal to the direct one. -/
lemma divisorPullback_comp_inv (f : X ⟶ S) (g : T ⟶ S) (h : U ⟶ T)
    (I : X.IdealSheafData) :
    ((I.comap (pullback.fst f g)).comap (pullback.fst (pullback.snd f g) h)).comap
        (familyPullbackCompIso (Over.mk f) g h).inv.left =
      I.comap (pullback.fst f (h ≫ g)) := by
  rw [← divisorPullback_comp, ← Scheme.IdealSheafData.comap_comp]
  simp

/-- Pulling a flat divisor along a flat ambient map leaves its map to the base flat. -/
lemma flat_comap_of_flat {Y : Scheme.{u}} (f : X ⟶ S) (k : Y ⟶ X)
    (I : X.IdealSheafData) [Flat k] [Flat (I.subschemeι ≫ f)] :
    Flat ((I.comap k).subschemeι ≫ k ≫ f) := by
  have he : (I.comap k).subschemeι ≫ k ≫ f =
      (I.comapIso k).hom ≫ pullback.snd k I.subschemeι ≫ (I.subschemeι ≫ f) := by
    rw [← pullback.condition_assoc, I.comapIso_hom_fst_assoc]
  rw [he]
  infer_instance

/-- Relative Cartier divisors restrict to open subschemes over the same base. -/
lemma RelativeEffectiveCartier.comap_of_isOpenImmersion {Y : Scheme.{u}}
    {f : X ⟶ S} {I : X.IdealSheafData} (hI : RelativeEffectiveCartier f I)
    (k : Y ⟶ X) [IsOpenImmersion k] :
    RelativeEffectiveCartier (k ≫ f) (I.comap k) := by
  let := hI.2
  exact ⟨hI.1.comap_of_isOpenImmersion k, flat_comap_of_flat f k I⟩

/-- Transport by an isomorphism retains both the ideal and the structure map. -/
lemma relativeEffectiveCartier_comap_iso_iff {Y : Scheme.{u}}
    (f : X ⟶ S) (I : X.IdealSheafData) (e : Y ≅ X) :
    RelativeEffectiveCartier (e.hom ≫ f) (I.comap e.hom) ↔
      RelativeEffectiveCartier f I := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comap_of_isOpenImmersion e.hom⟩
  have ht := h.comap_of_isOpenImmersion e.inv
  simpa only [Iso.inv_hom_id_assoc, ← Scheme.IdealSheafData.comap_comp,
    Iso.inv_hom_id, Scheme.IdealSheafData.comap_id] using ht

/-- Base change along an isomorphism preserves the full relative Cartier condition. -/
theorem relativeCartierBaseChange_of_isIso (f : X ⟶ S) (g : T ⟶ S)
    (I : X.IdealSheafData) [IsIso g] : RelativeCartierBaseChange f g I := by
  intro hI
  refine ⟨hI.1.comap_of_isOpenImmersion (pullback.fst f g), hI.flat_baseChange g⟩

/-- Under identity base change, the full relative condition is preserved. -/
theorem relativeCartierBaseChange_id (f : X ⟶ S) (I : X.IdealSheafData) :
    RelativeCartierBaseChange f (𝟙 S) I := by
  intro hI
  have h := hI.comap_of_isOpenImmersion (pullback.fst f (𝟙 S))
  simpa only [pullback.condition, Category.comp_id] using h

end Geometry

end FLT.Mazur.FCurve
