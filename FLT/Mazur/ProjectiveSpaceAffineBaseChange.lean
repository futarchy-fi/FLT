/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveSpaceCoefficientMap
public import FLT.Mazur.ProjectiveSpaceReindex

/-!
# Affine base change of projective space

Polynomial affine charts identify coefficient change with the actual scheme
fiber product, for arbitrary coefficient homomorphisms.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.ProjectiveSpace

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Coefficient change commutes with permutation of homogeneous coordinates. -/
@[reassoc]
lemma coefficientMap_reindex {ι κ : Type} (e : ι ≃ κ) :
    coefficientMap φ ι ≫ (reindexIso R e).hom =
      (reindexIso S e).hom ≫ coefficientMap φ κ := by
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _ ≫ Proj.map _ _
  rw [← Proj.map_comp, ← Proj.map_comp]
  congr 1
  ext p : 1
  exact MvPolynomial.map_rename φ e.symm p

/-- Polynomial chart coordinates commute with coefficient change. -/
lemma polynomialToChart_coefficient (n : ℕ) (p : MvPolynomial (Fin n) R) :
    coefficientChartRingMap φ (Fin (n + 1)) 0 (polynomialToChart R n p) =
      polynomialToChart S n (MvPolynomial.map φ p) := by
  have h : (coefficientChartRingMap φ (Fin (n + 1)) 0).comp
      (polynomialToChart R n).toRingHom =
      (polynomialToChart S n).toRingHom.comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change coefficientChartRingMap φ _ 0 (polynomialToChart R n (C r)) =
        polynomialToChart S n (MvPolynomial.map φ (C r))
      rw [map_C, polynomialToChart_C, polynomialToChart_C, coefficientChartRingMap_scalar]
    · intro i
      change coefficientChartRingMap φ _ 0 (polynomialToChart R n (X i)) =
        polynomialToChart S n (MvPolynomial.map φ (X i))
      rw [map_X, polynomialToChart_X, polynomialToChart_X, coefficientChartRingMap_coordinate]
  exact DFunLike.congr_fun h p

/-- The standard affine embedding is natural in the coefficient ring. -/
@[reassoc]
lemma affineChartEmbedding_coefficientMap (n : ℕ) :
    affineChartEmbedding S n ≫ coefficientMap φ (Fin (n + 1)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map φ)) ≫ affineChartEmbedding R n := by
  rw [affineChartEmbedding_eq, affineChartEmbedding_eq]
  change (Spec.map _ ≫ chartMap S _ 0) ≫ _ = _ ≫ Spec.map _ ≫ chartMap R _ 0
  rw [Category.assoc, chartMap_coefficientMap, ← Category.assoc, ← Spec.map_comp,
    ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := (chartPolynomialEquiv R n).surjective x
  change chartToPolynomial S n (coefficientChartRingMap φ _ 0 (polynomialToChart R n p)) =
    MvPolynomial.map φ (chartToPolynomial R n (polynomialToChart R n p))
  rw [polynomialToChart_coefficient, chartToPolynomial_polynomialToChart,
    chartToPolynomial_polynomialToChart]

/-- Polynomial affine spaces form a cartesian square under arbitrary coefficient change. -/
lemma polynomial_isPullback (n : ℕ) :
    IsPullback (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin n) φ)))
      (Spec.map (CommRingCat.ofHom (C : S →+* MvPolynomial (Fin n) S)))
      (Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial (Fin n) R)))
      (Spec.map (CommRingCat.ofHom φ)) := by
  apply isPullback_SpecMap_of_isPushout
  refine IsPushout.of_isColimit (c := PushoutCocone.mk
    (CommRingCat.ofHom (MvPolynomial.map (σ := Fin n) φ))
    (CommRingCat.ofHom (C : S →+* MvPolynomial (Fin n) S)) (by ext r; simp)) ?_
  refine PushoutCocone.IsColimit.mk _ (fun t ↦
    CommRingCat.ofHom (eval₂Hom t.inr.hom (fun i ↦ t.inl.hom (X i)))) ?_ ?_ ?_
  · intro t
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      change eval₂Hom t.inr.hom (fun i ↦ t.inl.hom (X i)) (MvPolynomial.map φ (C r)) =
        t.inl.hom (C r)
      rw [map_C, eval₂Hom_C]
      exact (congrArg (fun f ↦ f.hom r) t.condition).symm
    · intro i
      simp
  · intro t
    ext r
    simp
  · intro t m h₁ h₂
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa using congrArg (fun f ↦ f.hom r) h₂
    · intro i
      simpa using congrArg (fun f ↦ f.hom (X i)) h₁

variable (n : ℕ)

/-- The affine embedding obtained by moving the distinguished coordinate to `i`. -/
def affineChartAt (R : Type u) [CommRing R] (i : Fin (n + 1)) :
    Spec (.of (MvPolynomial (Fin n) R)) ⟶ space R (Fin (n + 1)) :=
  affineChartEmbedding R n ≫ (reindexIso R (Equiv.swap 0 i)).hom

instance (i : Fin (n + 1)) : IsOpenImmersion (affineChartAt n R i) := by
  dsimp [affineChartAt]
  infer_instance

/-- The moved affine embedding has the expected standard-chart image. -/
lemma affineChartAt_opensRange (i : Fin (n + 1)) :
    (affineChartAt n R i).opensRange = chart R (Fin (n + 1)) i := by
  change (affineChartEmbedding R n ≫ (reindexIso R (Equiv.swap 0 i)).hom).opensRange = _
  rw [Scheme.Hom.opensRange_comp, affineChartEmbedding_opensRange]
  have h : (reindexIso R (Equiv.swap 0 i)).hom ⁻¹ᵁ chart R (Fin (n + 1)) i =
      chart R (Fin (n + 1)) 0 := by simp
  rw [← h, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Hom.opensRange_of_isIso, top_inf_eq]

/-- Every moved chart still has the polynomial base projection. -/
@[reassoc]
lemma affineChartAt_baseProjection (i : Fin (n + 1)) :
    affineChartAt n R i ≫ baseProjection R (Fin (n + 1)) =
      Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial (Fin n) R)) := by
  simp [affineChartAt, affineChartEmbedding_baseProjection]

/-- The moved charts are natural under coefficient change. -/
@[reassoc]
lemma affineChartAt_coefficientMap (i : Fin (n + 1)) :
    affineChartAt n S i ≫ coefficientMap φ (Fin (n + 1)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map φ)) ≫ affineChartAt n R i := by
  simp only [affineChartAt, Category.assoc, ← coefficientMap_reindex,
    affineChartEmbedding_coefficientMap_assoc]

/-- Polynomial affine spaces cover every standard projective chart. -/
def coefficientAffineCover (R : Type u) [CommRing R] :
    (space R (Fin (n + 1))).OpenCover where
  I₀ := Fin (n + 1)
  X _ := Spec (.of (MvPolynomial (Fin n) R))
  f := affineChartAt n R
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_, fun _ ↦ inferInstance⟩
    intro x
    obtain ⟨i, hi⟩ := exists_mem_chart R (Fin (n + 1)) x
    rw [← affineChartAt_opensRange n i] at hi
    obtain ⟨y, hy⟩ := hi
    exact ⟨i, y, hy⟩

/-- The polynomial comparison identifies the inverse image of each chart. -/
lemma affineChartAt_isPullback (i : Fin (n + 1)) :
    IsPullback (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin n) φ)))
      (affineChartAt n S i) (affineChartAt n R i) (coefficientMap φ (Fin (n + 1))) := by
  apply IsOpenImmersion.isPullback
  · exact affineChartAt_coefficientMap φ n i
  · rw [affineChartAt_opensRange, affineChartAt_opensRange, coefficientMap_preimage_chart]

/-- Projective space commutes with arbitrary affine base change. -/
theorem coefficient_isPullback :
    IsPullback (coefficientMap φ (Fin (n + 1))) (baseProjection S (Fin (n + 1)))
      (baseProjection R (Fin (n + 1))) (Spec.map (CommRingCat.ofHom φ)) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (coefficientAffineCover n R)
  intro i
  let h := (affineChartAt_isPullback φ n i).flip
  have hlocal := polynomial_isPullback φ n
  rw [← affineChartAt_baseProjection n i, ← affineChartAt_baseProjection n i] at hlocal
  change IsPullback (pullback.snd _ _)
    (pullback.fst _ _ ≫ baseProjection S (Fin (n + 1)))
    (affineChartAt n R i ≫ baseProjection R (Fin (n + 1))) _
  apply hlocal.of_iso h.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.comp_id, coefficientAffineCover] using
      h.isoPullback_hom_snd.symm
  · simpa only [Iso.refl_hom, Category.comp_id, Category.assoc, coefficientAffineCover] using
      congrArg (fun k ↦ k ≫ baseProjection S (Fin (n + 1))) h.isoPullback_hom_fst.symm
  · simp
  · simp

/-- The actual scheme fiber product is the projective space over the new ring. -/
def affineBaseChangeIso : space S (Fin (n + 1)) ≅
    pullback (baseProjection R (Fin (n + 1))) (Spec.map (CommRingCat.ofHom φ)) :=
  (coefficient_isPullback φ n).isoPullback

/-- First projection of the comparison is the constructed coefficient map. -/
@[reassoc (attr := simp)]
lemma affineBaseChangeIso_hom_fst :
    (affineBaseChangeIso φ n).hom ≫ pullback.fst _ _ = coefficientMap φ (Fin (n + 1)) :=
  (coefficient_isPullback φ n).isoPullback_hom_fst

/-- Second projection of the comparison is the base projection over the new ring. -/
@[reassoc (attr := simp)]
lemma affineBaseChangeIso_hom_snd :
    (affineBaseChangeIso φ n).hom ≫ pullback.snd _ _ = baseProjection S (Fin (n + 1)) :=
  (coefficient_isPullback φ n).isoPullback_hom_snd

/-- Every standard open maps canonically into the affine base change. -/
def chartBaseChangeMap (i : Fin (n + 1)) :
    (chart S (Fin (n + 1)) i).toScheme ⟶
      pullback (baseProjection R (Fin (n + 1))) (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.lift ((chart S (Fin (n + 1)) i).ι ≫ coefficientMap φ _)
    ((chart S (Fin (n + 1)) i).ι ≫ baseProjection S _)
    (by simp only [Category.assoc, coefficientMap_baseProjection])

/-- The global comparison restricts to the canonical chart comparison. -/
@[reassoc]
lemma chartBaseChangeMap_eq (i : Fin (n + 1)) :
    chartBaseChangeMap φ n i = (chart S (Fin (n + 1)) i).ι ≫
      (affineBaseChangeIso φ n).hom := by
  apply pullback.hom_ext <;> simp [chartBaseChangeMap]

/-- Chart comparisons agree on every common subopen, hence on all overlaps. -/
lemma chartBaseChangeMap_overlap (i j : Fin (n + 1)) (W : (space S (Fin (n + 1))).Opens)
    (hi : W ≤ chart S (Fin (n + 1)) i) (hj : W ≤ chart S (Fin (n + 1)) j) :
    (space S (Fin (n + 1))).homOfLE hi ≫ chartBaseChangeMap φ n i =
      (space S (Fin (n + 1))).homOfLE hj ≫ chartBaseChangeMap φ n j := by
  simp [chartBaseChangeMap_eq]

/-- The cartesian square also holds for any finite coordinate set, including the empty set. -/
theorem coefficient_isPullback_of_finite (ι : Type) [Finite ι] :
    IsPullback (coefficientMap φ ι) (baseProjection S ι)
      (baseProjection R ι) (Spec.map (CommRingCat.ofHom φ)) := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  cases m with
  | zero =>
    apply Scheme.isPullback_of_openCover _ _ _ _ (standardChartCover R ι)
    intro i
    exact Fin.elim0 (e i)
  | succ n =>
    apply (coefficient_isPullback φ n).of_iso (reindexIso S e.symm)
      (reindexIso R e.symm) (Iso.refl _) (Iso.refl _)
    · exact coefficientMap_reindex φ e.symm
    · simp
    · simp
    · simp

/-- Base change for an arbitrary finite homogeneous coordinate set. -/
def finiteAffineBaseChangeIso (ι : Type) [Finite ι] : space S ι ≅
    pullback (baseProjection R ι) (Spec.map (CommRingCat.ofHom φ)) :=
  (coefficient_isPullback_of_finite φ ι).isoPullback

end FLT.Mazur.ProjectiveSpace
