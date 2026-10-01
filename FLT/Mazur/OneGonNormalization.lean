/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.OneGonRefinedDescent
public import FLT.Mazur.ProjectiveLineEndpoints

/-!
# The global normalization charts and the projective line

The affine normalization coordinate is t. The torus coordinate is
z = t/(t-1), so on the inverse projective chart w = 1/t = 1-z⁻¹.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open scoped LaurentPolynomial
open FLT.Mazur.OneGonTransition FLT.Mazur.OneGonMapGluing
open FLT.Mazur.OneGonRefinedDescent

namespace FLT.Mazur.OneGonNormalization

universe u
variable (K : Type u) [Field K]

/-- Reflection of the inverse affine coordinate. -/
def reflectionEquiv : K[X] ≃ₐ[K] K[X] :=
  Polynomial.algEquivOfCompEqX (1 - X) (1 - X) (by simp) (by simp)

@[simp]
theorem reflectionEquiv_apply (p : K[X]) :
    reflectionEquiv K p = p.comp (1 - X) := rfl

/-- The affine coordinate automorphism w ↦ 1-w. -/
def reflection : ProjectiveLine.chart K ≅ ProjectiveLine.chart K :=
  Scheme.Spec.mapIso (reflectionEquiv K).toRingEquiv.toCommRingCatIso.op

@[simp]
theorem reflection_hom : (reflection K).hom =
    Spec.map (CommRingCat.ofHom (reflectionEquiv K).toRingHom) := rfl

theorem reflection_square : (reflection K).hom ≫ (reflection K).hom = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (reflectionEquiv K).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (reflectionEquiv K).toRingHom) = _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply ConcreteCategory.hom_ext
  intro p
  change (p.comp (1 - X)).comp (1 - X) = p
  simp [Polynomial.comp_assoc]

/-- The torus maps into the inverse projective chart by w = 1-z⁻¹. -/
def torusToRight : ProjectiveLine.overlap K ⟶ ProjectiveLine.chart K :=
  ProjectiveLine.overlapRight K ≫ (reflection K).hom

instance : IsOpenImmersion (torusToRight K) := by
  unfold torusToRight
  infer_instance

/-- The puncture with its ordinary t-coordinate maps to the standard projective overlap. -/
def toOverlap : Spec (.of (puncture K)) ⟶ ProjectiveLine.overlap K :=
  (localizationSpecIso K).hom ≫ torusOpen K

instance : IsOpenImmersion (toOverlap K) := by
  unfold toOverlap
  infer_instance

theorem toOverlap_eq : toOverlap K =
    Spec.map (CommRingCat.ofHom (torusRestriction K)) := by
  simp only [toOverlap, torusRestriction, CommRingCat.ofHom_comp, Spec.map_comp]
  rfl

@[reassoc]
theorem toOverlap_left :
    toOverlap K ≫ ProjectiveLine.overlapLeft K = punctureToLine := by
  rw [toOverlap_eq, ProjectiveLine.overlapLeft, punctureToLine, ← Spec.map_comp]
  congr 1
  ext r
  · simpa using (IsScalarTower.algebraMap_apply K K[X] (puncture K) r)
  · simp

theorem overlapMap_neg :
    overlapMap K (LaurentPolynomial.T (-1)) = (↑(mobius K)⁻¹ : puncture K) := by
  apply (mobius K).isUnit.mul_left_cancel
  rw [← overlapMap_T, ← map_mul, ← LaurentPolynomial.T_add]
  simp

theorem torusRestriction_neg :
    torusRestriction K (LaurentPolynomial.T (-1)) = (↑(coordinate K)⁻¹ : puncture K) := by
  apply (coordinate K).isUnit.mul_left_cancel
  rw [← torusRestriction_T, ← map_mul, ← LaurentPolynomial.T_add]
  simp only [add_neg_cancel, LaurentPolynomial.T_zero, map_one]
  rw [torusRestriction_T]
  exact (Units.mul_inv (coordinate K)).symm

theorem one_sub_mobius_inv :
    1 - (↑(mobius K)⁻¹ : puncture K) = (↑(coordinate K)⁻¹ : puncture K) := by
  change 1 - (↑((coordinate K * (difference K)⁻¹)⁻¹) : puncture K) = _
  simp only [mul_inv_rev, inv_inv, Units.val_mul, difference_val]
  have h := Units.mul_inv (coordinate K)
  change (coordinate K : puncture K) * ↑(coordinate K)⁻¹ = 1 at h
  rw [sub_mul, one_mul, h]
  ring

@[reassoc]
theorem toOverlap_right :
    toTorus K ≫ torusToRight K = toOverlap K ≫ ProjectiveLine.overlapRight K := by
  have he :
      (overlapMap K).comp (LaurentPolynomial.invert.toRingHom.comp
        (Polynomial.toLaurent.comp (reflectionEquiv K).toRingHom)) =
      (torusRestriction K).comp
        (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) := by
    ext r
    · simp
    · change overlapMap K (LaurentPolynomial.invert (toLaurent ((X : K[X]).comp (1 - X)))) =
        torusRestriction K (LaurentPolynomial.invert (toLaurent (X : K[X])))
      simp only [X_comp, map_sub, map_one, toLaurent_X, LaurentPolynomial.invert_T]
      rw [overlapMap_neg, torusRestriction_neg, one_sub_mobius_inv]
  have h := congrArg (fun φ : K[X] →+* puncture K ↦ Spec.map (CommRingCat.ofHom φ)) he
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    toTorus_eq_specMap, toOverlap_eq, torusToRight, ProjectiveLine.overlapRight,
    ProjectiveLine.inversion_hom, ProjectiveLine.overlapLeft, reflection_hom] using h

/-- Precomposing by an isomorphism does not change the image of a chart. -/
theorem range_iso_comp {A B C : Scheme.{u}} (e : A ≅ B) (f : B ⟶ C) :
    Set.range (e.hom ≫ f) = Set.range f := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e.hom y, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨e.inv y, ?_⟩
    have he := congrArg (fun g : B ⟶ B ↦ g y) e.inv_hom_id
    change e.hom (e.inv y) = y at he
    change f (e.hom (e.inv y)) = f y
    rw [he]

theorem range_overlapRight :
    Set.range (ProjectiveLine.overlapRight K) =
      (PrimeSpectrum.basicOpen (X : K[X]) : Set (PrimeSpectrum K[X])) := by
  rw [ProjectiveLine.overlapRight, range_iso_comp]
  exact PrimeSpectrum.localization_away_comap_range K[T;T⁻¹] X

theorem range_toOverlap :
    Set.range (toOverlap K) =
      (PrimeSpectrum.basicOpen (LaurentPolynomial.T 1 - 1 : K[T;T⁻¹]) :
        Set (PrimeSpectrum K[T;T⁻¹])) := by
  rw [toOverlap, range_iso_comp]
  exact range_torusOpen K

/-- The second normalization chart excludes precisely the inverse-coordinate point one. -/
theorem range_torusToRight :
    Set.range (torusToRight K) =
      (PrimeSpectrum.basicOpen (1 - X : K[X]) : Set (PrimeSpectrum K[X])) := by
  ext p
  constructor
  · rintro ⟨y, rfl⟩
    change LaurentPolynomial.invert (toLaurent ((1 - X : K[X]).comp (1 - X))) ∉ y.asIdeal
    have := y.isPrime
    simpa using y.asIdeal.notMem_of_isUnit (LaurentPolynomial.isUnit_T (R := K) (-1))
  · intro hp
    have hp' : (reflection K).hom p ∈ Set.range (ProjectiveLine.overlapRight K) := by
      apply (Set.ext_iff.mp (range_overlapRight K) _).mpr
      change (X : K[X]).comp (1 - X) ∉ p.asIdeal
      simpa only [X_comp] using (PrimeSpectrum.mem_basicOpen _ _).mp hp
    obtain ⟨y, hy⟩ := hp'
    refine ⟨y, ?_⟩
    change (reflection K).hom (ProjectiveLine.overlapRight K y) = p
    rw [hy]
    exact congrArg (fun g : ProjectiveLine.chart K ⟶ ProjectiveLine.chart K ↦ g p)
      (reflection_square K)

/-- These two open charts cover the whole inverse affine chart. -/
theorem right_cover (p : ProjectiveLine.chart K) :
    p ∈ Set.range (ProjectiveLine.overlapRight K) ∨ p ∈ Set.range (torusToRight K) := by
  by_cases hp : (X : K[X]) ∈ p.asIdeal
  · right
    apply (Set.ext_iff.mp (range_torusToRight K) p).mpr
    intro h
    have := p.isPrime
    exact p.asIdeal.notMem_of_isUnit isUnit_one
      (by simpa using p.asIdeal.add_mem h hp)
  · left
    exact (Set.ext_iff.mp (range_overlapRight K) p).mpr hp

/-- The common puncture is exactly the intersection of the two right-chart opens. -/
theorem overlap_isPullback :
    IsPullback (toTorus K) (toOverlap K) (torusToRight K)
      (ProjectiveLine.overlapRight K) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (toOverlap_right K).symm
  have h₁ : (torusToRight K).opensRange = PrimeSpectrum.basicOpen (1 - X : K[X]) :=
    TopologicalSpace.Opens.ext (range_torusToRight K)
  have h₂ : (toOverlap K).opensRange =
      PrimeSpectrum.basicOpen (LaurentPolynomial.T 1 - 1 : K[T;T⁻¹]) :=
    TopologicalSpace.Opens.ext (range_toOverlap K)
  rw [h₁, h₂]
  ext p
  change LaurentPolynomial.invert (toLaurent (1 - X : K[X])) ∉ p.asIdeal ↔
    LaurentPolynomial.T 1 - 1 ∉ p.asIdeal
  simp only [map_sub, map_one, toLaurent_X, LaurentPolynomial.invert_T]
  have he : (LaurentPolynomial.T 1 : K[T;T⁻¹]) * (1 - LaurentPolynomial.T (-1)) =
      LaurentPolynomial.T 1 - 1 := by
    rw [mul_sub, mul_one, ← LaurentPolynomial.T_add]
    simp
  have hu : (LaurentPolynomial.T 1 : K[T;T⁻¹]) ∉ p.asIdeal := by
    have := p.isPrime
    exact p.asIdeal.notMem_of_isUnit (LaurentPolynomial.isUnit_T 1)
  rw [← he, p.isPrime.mul_mem_iff_mem_or_mem, or_iff_right hu]

/-- The scheme obtained by gluing the actual normalization charts. -/
def scheme : Scheme.{u} := pushout (punctureToLine (K := K)) (toTorus K)

/-- The affine normalization chart. -/
def line : ProjectiveLine.chart K ⟶ scheme K := pushout.inl _ _

/-- The unchanged torus chart of the normalization. -/
def torus : ProjectiveLine.overlap K ⟶ scheme K := pushout.inr _ _

theorem exists_rightMap :
    ∃ r : ProjectiveLine.chart K ⟶ scheme K,
      ProjectiveLine.overlapRight K ≫ r = ProjectiveLine.overlapLeft K ≫ line K ∧
      torusToRight K ≫ r = torus K := by
  apply exists_glue_two (ProjectiveLine.overlapRight K) (torusToRight K) (right_cover K)
  apply (cancel_epi (overlap_isPullback K).flip.isoPullback.hom).mp
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]
  rw [toOverlap_left]
  exact pushout.condition

/-- The inverse affine chart maps to the glued normalization by its refined cover. -/
def rightMap : ProjectiveLine.chart K ⟶ scheme K := (exists_rightMap K).choose

@[reassoc (attr := simp)]
theorem overlap_rightMap :
    ProjectiveLine.overlapRight K ≫ rightMap K =
      ProjectiveLine.overlapLeft K ≫ line K := (exists_rightMap K).choose_spec.1

@[reassoc (attr := simp)]
theorem torus_rightMap : torusToRight K ≫ rightMap K = torus K :=
  (exists_rightMap K).choose_spec.2

/-- The normalization charts map to the fixed projective line. -/
def toProjective : scheme K ⟶ ProjectiveLine.scheme K :=
  pushout.desc (ProjectiveLine.left K) (torusToRight K ≫ ProjectiveLine.right K) (by
    rw [← toOverlap_left K, Category.assoc, ProjectiveLine.overlap_condition,
      ← Category.assoc, ← toOverlap_right K, Category.assoc])

/-- The inverse map is obtained from the two fixed projective charts. -/
def fromProjective : ProjectiveLine.scheme K ⟶ scheme K :=
  pushout.desc (line K) (rightMap K) (overlap_rightMap K).symm

@[reassoc (attr := simp)]
theorem line_toProjective : line K ≫ toProjective K = ProjectiveLine.left K :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem torus_toProjective :
    torus K ≫ toProjective K = torusToRight K ≫ ProjectiveLine.right K :=
  pushout.inr_desc _ _ _

@[reassoc (attr := simp)]
theorem left_fromProjective : ProjectiveLine.left K ≫ fromProjective K = line K :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem right_fromProjective : ProjectiveLine.right K ≫ fromProjective K = rightMap K :=
  pushout.inr_desc _ _ _

theorem toProjective_fromProjective :
    toProjective K ≫ fromProjective K = 𝟙 _ := by
  apply pushout.hom_ext
  · change line K ≫ _ = line K ≫ _
    simp
  · change torus K ≫ _ = torus K ≫ _
    simp

theorem rightMap_toProjective : rightMap K ≫ toProjective K = ProjectiveLine.right K := by
  apply hom_ext_two (ProjectiveLine.overlapRight K) (torusToRight K) (right_cover K)
  · simp only [overlap_rightMap_assoc, line_toProjective]
    exact ProjectiveLine.overlap_condition K
  · simp

theorem fromProjective_toProjective :
    fromProjective K ≫ toProjective K = 𝟙 _ := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫ _ = ProjectiveLine.left K ≫ _
    simp
  · change ProjectiveLine.right K ≫ _ = ProjectiveLine.right K ≫ _
    simp [rightMap_toProjective]

/-- The global normalization charts are isomorphic to the specified projective line. -/
def projectiveIso : scheme K ≅ ProjectiveLine.scheme K where
  hom := toProjective K
  inv := fromProjective K
  hom_inv_id := toProjective_fromProjective K
  inv_hom_id := fromProjective_toProjective K

/-- The morphism from the normalization charts to the pinched one-gon. -/
def toOneGon : scheme K ⟶ OneGonGluing.scheme K :=
  pushout.desc (OneGonPinchingAlgebra.toPinching ≫ OneGonGluing.node K)
    (OneGonGluing.torus K) (by
      rw [← Category.assoc, puncture_toPinching]
      exact OneGonGluing.overlap_condition K)

@[reassoc (attr := simp)]
theorem line_toOneGon :
    line K ≫ toOneGon K = OneGonPinchingAlgebra.toPinching ≫ OneGonGluing.node K :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem torus_toOneGon : torus K ≫ toOneGon K = OneGonGluing.torus K :=
  pushout.inr_desc _ _ _

/-- The resulting global map from the fixed projective line to the one-gon. -/
def projectiveToOneGon : ProjectiveLine.scheme K ⟶ OneGonGluing.scheme K :=
  (projectiveIso K).inv ≫ toOneGon K

@[reassoc (attr := simp)]
theorem left_projectiveToOneGon :
    ProjectiveLine.left K ≫ projectiveToOneGon K =
      OneGonPinchingAlgebra.toPinching ≫ OneGonGluing.node K := by
  simp [projectiveToOneGon, projectiveIso]

/-- In the t-coordinate, the two branches to be pinched are zero and one. -/
theorem endpoints_projectiveToOneGon :
    OneGonLocalFactorization.endpointSection 0 ≫ ProjectiveLine.left K ≫ projectiveToOneGon K =
      OneGonLocalFactorization.endpointSection 1 ≫ ProjectiveLine.left K ≫
        projectiveToOneGon K := by
  rw [left_projectiveToOneGon]
  have he : OneGonLocalFactorization.endpointSection (0 : K) ≫
      OneGonPinchingAlgebra.toPinching =
      OneGonLocalFactorization.endpointSection (1 : K) ≫ OneGonPinchingAlgebra.toPinching := by
    rw [OneGonLocalFactorization.endpointSection, OneGonLocalFactorization.endpointSection,
      OneGonPinchingAlgebra.toPinching, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply ConcreteCategory.hom_ext
    intro b
    exact (PolygonNodePresentation.mem_B _).mp b.property
  simpa only [Category.assoc] using congrArg (fun m ↦ m ≫ OneGonGluing.node K) he

@[reassoc (attr := simp)]
theorem torus_projectiveToOneGon :
    torusToRight K ≫ ProjectiveLine.right K ≫ projectiveToOneGon K =
      OneGonGluing.torus K := by
  rw [← Category.assoc, ← torus_toProjective, projectiveToOneGon]
  change (torus K ≫ toProjective K) ≫ fromProjective K ≫ toOneGon K = _
  rw [Category.assoc, ← Category.assoc (toProjective K),
    toProjective_fromProjective, Category.id_comp, torus_toOneGon]

instance : IsIso (toProjective K) :=
  inferInstanceAs (IsIso (projectiveIso K).hom)

/-- The global map has the pinching universal property for the marked points t=0 and t=1. -/
theorem existsUnique_projective_desc {T : Scheme.{u}}
    (f : ProjectiveLine.scheme K ⟶ T)
    (hf : OneGonLocalFactorization.endpointSection 0 ≫ ProjectiveLine.left K ≫ f =
      OneGonLocalFactorization.endpointSection 1 ≫ ProjectiveLine.left K ≫ f) :
    ∃! d : OneGonGluing.scheme K ⟶ T, projectiveToOneGon K ≫ d = f := by
  have hc : punctureToLine ≫ (ProjectiveLine.left K ≫ f) =
      toTorus K ≫ (torusToRight K ≫ ProjectiveLine.right K ≫ f) := by
    have h₀ : punctureToLine ≫ ProjectiveLine.left K =
        toTorus K ≫ (torusToRight K ≫ ProjectiveLine.right K) := by
      rw [← toOverlap_left K, Category.assoc, ProjectiveLine.overlap_condition,
        ← Category.assoc, ← toOverlap_right K, Category.assoc]
    simpa only [Category.assoc] using congrArg (fun m ↦ m ≫ f) h₀
  let d := OneGonRefinedDescent.gluedMap (ProjectiveLine.left K ≫ f) hf
    (torusToRight K ≫ ProjectiveLine.right K ≫ f) hc
  refine ⟨d, ?_, ?_⟩
  · apply (cancel_epi (toProjective K)).mp
    apply pushout.hom_ext
    · change line K ≫ _ = line K ≫ _
      simp only [line_toProjective_assoc, left_projectiveToOneGon_assoc]
      exact OneGonRefinedDescent.normalization_gluedMap _ _ _ _
    · change torus K ≫ _ = torus K ≫ _
      simp only [torus_toProjective_assoc, torus_projectiveToOneGon_assoc]
      exact OneGonRefinedDescent.torus_gluedMap _ _ _ _
  · intro e he
    apply OneGonRefinedDescent.gluedMap_unique
    · have hh := congrArg (fun m ↦ ProjectiveLine.left K ≫ m) he
      simpa only [left_projectiveToOneGon_assoc, Category.assoc] using hh
    · have hh := congrArg
        (fun m ↦ torusToRight K ≫ ProjectiveLine.right K ≫ m) he
      simpa only [torus_projectiveToOneGon_assoc] using hh

end FLT.Mazur.OneGonNormalization
