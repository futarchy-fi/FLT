/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveProductChartCover

/-!
# Intersections of projective product charts

The tensor product of the two homogeneous overlap rings represents the
intersection of two standard charts in the actual projective product.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

open scoped TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.ProjectiveSpace

section Tensor

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- First projection from a tensor spectrum. -/
abbrev tensorSpecFst : Spec (.of (A ⊗[R] B)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)

/-- Second projection from a tensor spectrum. -/
abbrev tensorSpecSnd : Spec (.of (A ⊗[R] B)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)

/-- The tensor spectrum has the fiber-product universal property over the base. -/
lemma tensorSpecIsPullback :
    IsPullback (tensorSpecFst R A B) (tensorSpecSnd R A B)
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (pullbackSpecIso R A B).symm
    (pullbackSpecIso_inv_fst R A B) (pullbackSpecIso_inv_snd R A B)
  have h := congrArg (fun f ↦ (pullbackSpecIso R A B).inv ≫ f)
    (pullback.condition (f := Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (g := Spec.map (CommRingCat.ofHom (algebraMap R B))))
  simpa only [← Category.assoc, pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd,
    tensorSpecFst, tensorSpecSnd, AlgHom.toRingHom_eq_coe] using h

variable {A B} {C D : Type u} [CommRing C] [CommRing D] [Algebra R C] [Algebra R D]

@[reassoc]
lemma tensorSpecMap_fst (f : A →ₐ[R] C) (g : B →ₐ[R] D) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map f g).toRingHom) ≫
        tensorSpecFst R A B =
      tensorSpecFst R C D ≫ Spec.map (CommRingCat.ofHom f.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  simp

@[reassoc]
lemma tensorSpecMap_snd (f : A →ₐ[R] C) (g : B →ₐ[R] D) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map f g).toRingHom) ≫
        tensorSpecSnd R A B =
      tensorSpecSnd R C D ≫ Spec.map (CommRingCat.ofHom g.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  simp

@[reassoc]
lemma specAlgHom_base (f : A →ₐ[R] C) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact f.commutes r

end Tensor

variable (R : Type u) [CommRing R] (ι κ : Type u)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The first overlap restriction is the inclusion of the homogeneous overlap. -/
@[reassoc]
lemma chartOverlapLeft_chartMap (i k : ι) :
    Spec.map (CommRingCat.ofHom (chartOverlapLeft R ι i k).toRingHom) ≫
      chartMap R ι i = overlapMap R ι i k :=
  toOverlap_chartMap R ι i k

/-- The second overlap restriction has the same image in projective space. -/
@[reassoc]
lemma chartOverlapRight_chartMap (i k : ι) :
    Spec.map (CommRingCat.ofHom (chartOverlapRight R ι i k).toRingHom) ≫
      chartMap R ι k = overlapMap R ι i k :=
  Proj.SpecMap_awayMap_awayι (grading R ι) (isHomogeneous_X R k)
    (by decide) (isHomogeneous_X R i) (mul_comm (X i) (X k))

/-- Homogeneous overlap spectra are the actual intersections of standard charts. -/
lemma chartOverlapIsPullback (i k : ι) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartOverlapLeft R ι i k).toRingHom))
      (Spec.map (CommRingCat.ofHom (chartOverlapRight R ι i k).toRingHom))
      (chartMap R ι i) (chartMap R ι k) := by
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (chartOverlapLeft R ι i k).toRingHom)) := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (toOverlap R ι i k)))
    infer_instance
  refine (IsOpenImmersion.isPullback
    (Spec.map (CommRingCat.ofHom (chartOverlapRight R ι i k).toRingHom))
    (Spec.map (CommRingCat.ofHom (chartOverlapLeft R ι i k).toRingHom))
    (chartMap R ι k) (chartMap R ι i) ?_ ?_).flip
  · exact (toOverlap_chartMap R ι i k).trans
      (chartOverlapRight_chartMap R ι i k).symm
  · have h : (chartMap R ι k).opensRange = chart R ι k :=
      (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (chart R ι k).opensRange_ι
    rw [h, chartMap_preimage_chart]
    exact (toOverlap_image_top R ι i k).symm.trans
      (Scheme.Hom.image_top_eq_opensRange _)

/-- First restriction from a product chart intersection. -/
abbrev productOverlapLeftMap (i k : ι) (j l : κ) :=
  Spec.map (CommRingCat.ofHom (segreOverlapLeft R ι κ i k j l).toRingHom)

/-- Second restriction from a product chart intersection. -/
abbrev productOverlapRightMap (i k : ι) (j l : κ) :=
  Spec.map (CommRingCat.ofHom (segreOverlapRight R ι κ i k j l).toRingHom)

/-- The two restrictions have the same map into the actual projective product. -/
lemma productOverlap_condition (i k : ι) (j l : κ) :
    productOverlapLeftMap R ι κ i k j l ≫ productChartMap R ι κ i j =
      productOverlapRightMap R ι κ i k j l ≫ productChartMap R ι κ k l := by
  apply pullback.hom_ext
  · simp only [Category.assoc, productChartMap_fst, productOverlapLeftMap,
      productOverlapRightMap, segreOverlapLeft, segreOverlapRight,
      tensorSpecMap_fst_assoc, chartOverlapLeft_chartMap, chartOverlapRight_chartMap]
  · simp only [Category.assoc, productChartMap_snd, productOverlapLeftMap,
      productOverlapRightMap, segreOverlapLeft, segreOverlapRight,
      tensorSpecMap_snd_assoc, chartOverlapLeft_chartMap, chartOverlapRight_chartMap]

/-- Equality can be checked after restricting an overlap to its first chart. -/
lemma productOverlap_hom_ext (i k : ι) (j l : κ) {T : Scheme.{u}}
    {f g : T ⟶ Spec (.of (segreOverlapRing R ι κ i k j l))}
    (h : f ≫ productOverlapLeftMap R ι κ i k j l =
      g ≫ productOverlapLeftMap R ι κ i k j l) : f = g := by
  have := (chartOverlapIsPullback R ι i k).mono_fst_of_mono
  have := (chartOverlapIsPullback R κ j l).mono_fst_of_mono
  apply (tensorSpecIsPullback R (overlapRing R ι i k) (overlapRing R κ j l)).hom_ext
  · apply (cancel_mono
      (Spec.map (CommRingCat.ofHom (chartOverlapLeft R ι i k).toRingHom))).mp
    have h' := congrArg (fun a ↦ a ≫
      tensorSpecFst R (chartRing R ι i) (chartRing R κ j)) h
    simpa only [Category.assoc, productOverlapLeftMap, segreOverlapLeft,
      tensorSpecMap_fst] using h'
  · apply (cancel_mono
      (Spec.map (CommRingCat.ofHom (chartOverlapLeft R κ j l).toRingHom))).mp
    have h' := congrArg (fun a ↦ a ≫
      tensorSpecSnd R (chartRing R ι i) (chartRing R κ j)) h
    simpa only [Category.assoc, productOverlapLeftMap, segreOverlapLeft,
      tensorSpecMap_snd] using h'

/-- A compatible pair of maps lifts to the tensor of the actual chart intersections. -/
lemma productOverlap_exists_lift (i k : ι) (j l : κ) {T : Scheme.{u}}
    (f : T ⟶ Spec (.of (segreSourceRing R ι κ i j)))
    (g : T ⟶ Spec (.of (segreSourceRing R ι κ k l)))
    (h : f ≫ productChartMap R ι κ i j = g ≫ productChartMap R ι κ k l) :
    ∃ t : T ⟶ Spec (.of (segreOverlapRing R ι κ i k j l)),
      t ≫ productOverlapLeftMap R ι κ i k j l = f ∧
        t ≫ productOverlapRightMap R ι κ i k j l = g := by
  have hi : (f ≫ tensorSpecFst R (chartRing R ι i) (chartRing R κ j)) ≫
      chartMap R ι i =
      (g ≫ tensorSpecFst R (chartRing R ι k) (chartRing R κ l)) ≫ chartMap R ι k := by
    simpa only [Category.assoc, productChartMap_fst] using
      congrArg (fun a ↦ a ≫ pullback.fst (baseProjection R ι) (baseProjection R κ)) h
  have hj : (f ≫ tensorSpecSnd R (chartRing R ι i) (chartRing R κ j)) ≫
      chartMap R κ j =
      (g ≫ tensorSpecSnd R (chartRing R ι k) (chartRing R κ l)) ≫ chartMap R κ l := by
    simpa only [Category.assoc, productChartMap_snd] using
      congrArg (fun a ↦ a ≫ pullback.snd (baseProjection R ι) (baseProjection R κ)) h
  obtain ⟨a, ha, ha'⟩ := (chartOverlapIsPullback R ι i k).exists_lift _ _ hi
  obtain ⟨b, hb, hb'⟩ := (chartOverlapIsPullback R κ j l).exists_lift _ _ hj
  have hab : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R (overlapRing R ι i k))) =
      b ≫ Spec.map (CommRingCat.ofHom (algebraMap R (overlapRing R κ j l))) := by
    rw [← specAlgHom_base R (chartOverlapLeft R ι i k),
      ← specAlgHom_base R (chartOverlapLeft R κ j l), ← Category.assoc, ha,
      ← Category.assoc, hb, Category.assoc, Category.assoc]
    exact congrArg (fun a ↦ f ≫ a)
      (tensorSpecIsPullback R (chartRing R ι i) (chartRing R κ j)).w
  obtain ⟨t, ht, ht'⟩ :=
    (tensorSpecIsPullback R (overlapRing R ι i k) (overlapRing R κ j l)).exists_lift _ _ hab
  refine ⟨t, ?_, ?_⟩
  · apply (tensorSpecIsPullback R (chartRing R ι i) (chartRing R κ j)).hom_ext
    · rw [Category.assoc, productOverlapLeftMap, segreOverlapLeft,
        tensorSpecMap_fst, ← Category.assoc, ht, ha]
    · rw [Category.assoc, productOverlapLeftMap, segreOverlapLeft,
        tensorSpecMap_snd, ← Category.assoc, ht', hb]
  · apply (tensorSpecIsPullback R (chartRing R ι k) (chartRing R κ l)).hom_ext
    · rw [Category.assoc, productOverlapRightMap, segreOverlapRight,
        tensorSpecMap_fst, ← Category.assoc, ht, ha']
    · rw [Category.assoc, productOverlapRightMap, segreOverlapRight,
        tensorSpecMap_snd, ← Category.assoc, ht', hb']

/-- Tensor-overlap spectra represent the intersections in the projective product. -/
lemma productOverlapIsPullback (i k : ι) (j l : κ) :
    IsPullback (productOverlapLeftMap R ι κ i k j l)
      (productOverlapRightMap R ι κ i k j l)
      (productChartMap R ι κ i j) (productChartMap R ι κ k l) := by
  have h (s : PullbackCone (productChartMap R ι κ i j) (productChartMap R ι κ k l)) :=
    productOverlap_exists_lift R ι κ i k j l s.fst s.snd s.condition
  choose lift hl hr using h
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (productOverlap_condition R ι κ i k j l) lift hl hr ?_)
  intro s m hm _
  exact productOverlap_hom_ext R ι κ i k j l (hm.trans (hl s).symm)

/-- The constructed comparison with the pullback of two actual product chart maps. -/
def productOverlapIso (i k : ι) (j l : κ) :
    Spec (.of (segreOverlapRing R ι κ i k j l)) ≅
      pullback (productChartMap R ι κ i j) (productChartMap R ι κ k l) :=
  (productOverlapIsPullback R ι κ i k j l).isoPullback

/-- First projection is exactly the spectrum of the left tensor restriction. -/
@[reassoc (attr := simp)]
lemma productOverlapIso_hom_fst (i k : ι) (j l : κ) :
    (productOverlapIso R ι κ i k j l).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (segreOverlapLeft R ι κ i k j l).toRingHom) :=
  (productOverlapIsPullback R ι κ i k j l).isoPullback_hom_fst

/-- Second projection is exactly the spectrum of the right tensor restriction. -/
@[reassoc (attr := simp)]
lemma productOverlapIso_hom_snd (i k : ι) (j l : κ) :
    (productOverlapIso R ι κ i k j l).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (segreOverlapRight R ι κ i k j l).toRingHom) :=
  (productOverlapIsPullback R ι κ i k j l).isoPullback_hom_snd

end FLT.Mazur.ProjectiveSpace
