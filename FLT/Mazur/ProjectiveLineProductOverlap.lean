/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineProductCharts
public import FLT.Mazur.PolygonScalingNaturality
public import FLT.Mazur.BinaryOpenDescent
/-!
# Laurent intersection of the projective-line product charts

After any affine parameter base change, the polynomial charts meet in the
Laurent spectrum with reciprocal coordinates. The computed inverse-image
open makes this a cartesian square and an open-cover pushout.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Polynomial LaurentPolynomial
universe u
namespace FLT.Mazur.ProjectiveLineProductOverlap
open ProjectiveLineProductCharts
variable (K S : Type u) [Field K] [CommRing S] [Algebra K S]

/-- The punctured first product chart. -/
def left : Spec (.of S[T;T⁻¹]) ⟶ Spec (.of S[X]) :=
  Spec.map (CommRingCat.ofHom Polynomial.toLaurent)
/-- Invert the chart coordinate over the parameter ring. -/
def inversion : Spec (.of S[T;T⁻¹]) ≅ Spec (.of S[T;T⁻¹]) :=
  Scheme.Spec.mapIso (LaurentPolynomial.invert.toRingEquiv.toCommRingCatIso.op)
/-- The inversion morphism on coordinate rings. -/
@[simp] theorem inversion_hom : (inversion S).hom =
    Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert (R := S)).toRingHom) := rfl
/-- The punctured second chart uses the reciprocal coordinate. -/
def right : Spec (.of S[T;T⁻¹]) ⟶ Spec (.of S[X]) :=
  (inversion S).hom ≫ left S
instance left_open : IsOpenImmersion (left S) :=
  IsOpenImmersion.of_isLocalization (Polynomial.X : S[X])
instance right_open : IsOpenImmersion (right S) := by unfold right; infer_instance

/-- The Laurent coefficient map to the original overlap. -/
def coeff : Spec (.of S[T;T⁻¹]) ⟶ ProjectiveLine.overlap K :=
  Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap (algebraMap K S)))

/-- The first punctured chart commutes with coefficient change. -/
theorem left_coeff : left S ≫
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap K S))) =
    coeff K S ≫ ProjectiveLine.overlapLeft K := by
  simpa only [left, coeff, ProjectiveLine.overlapLeft, CommRingCat.ofHom_comp, Spec.map_comp]
    using congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
      (PolygonScalingNaturality.coeffMap_toLaurent (algebraMap K S)).symm

/-- The reciprocal punctured chart commutes with coefficient change. -/
theorem right_coeff : right S ≫
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap K S))) =
    coeff K S ≫ ProjectiveLine.overlapRight K := by
  have h : LaurentPolynomial.invert.toRingHom.comp
      (Polynomial.toLaurent.comp (Polynomial.mapRingHom (algebraMap K S))) =
      (PolygonScalingNaturality.coeffMap (algebraMap K S)).comp
        (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) := by
    ext <;> simp
  simpa only [right, inversion_hom, left, coeff, ProjectiveLine.overlapRight,
    ProjectiveLine.overlapLeft, ProjectiveLine.inversion_hom, CommRingCat.ofHom_comp,
    Spec.map_comp, Category.assoc] using
    congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) h

/-- The two punctured product charts agree in the fiber product. -/
theorem condition : left S ≫ productChartMap K S false =
    right S ≫ productChartMap K S true := by
  apply pullback.hom_ext
  · simp only [Category.assoc, productChartMap_fst]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
    simp only [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    simp
  · simp only [Category.assoc, productChartMap_snd]
    rw [← Category.assoc, left_coeff, ← Category.assoc, right_coeff]
    simpa only [Category.assoc, chartCover, Bool.false_eq_true, ↓reduceIte] using
      congrArg (fun f ↦ coeff K S ≫ f) (ProjectiveLine.overlap_condition K)

/-- A point shared by the original charts lifts to their Laurent overlap. -/
theorem original_intersection (x y : ProjectiveLine.chart K)
    (h : ProjectiveLine.left K x = ProjectiveLine.right K y) :
    ∃ z, ProjectiveLine.overlapLeft K z = x := by
  obtain ⟨i, fi, fj, z, hx, _⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff
    (span (ProjectiveLine.overlapLeft K) (ProjectiveLine.overlapRight K))).mp h
  cases i with
  | none => cases fi; cases fj; exact ⟨z, hx⟩
  | some i => cases i with
    | left => cases fj
    | right => cases fi

/-- The inverse image of the second product chart is exactly the puncture. -/
theorem preimage_right : (productChartMap K S false) ⁻¹ᵁ
    (productChartMap K S true).opensRange = (left S).opensRange := by
  ext x
  change productChartMap K S false x ∈ Set.range (productChartMap K S true) ↔
    x ∈ Set.range (left S)
  constructor
  · rintro ⟨y, hy⟩
    have he := congrArg (pullback.snd (parameterToBase K S) (ProjectiveLine.toBase K)) hy
    change (productChartMap K S true ≫ pullback.snd _ _) y =
      (productChartMap K S false ≫ pullback.snd _ _) x at he
    simp only [productChartMap_snd, chartCover, ↓reduceIte, Bool.false_eq_true] at he
    obtain ⟨z, hz⟩ := original_intersection K _ _ he.symm
    have hx : PrimeSpectrum.comap (Polynomial.mapRingHom (algebraMap K S)) x ∈
        Set.range (ProjectiveLine.overlapLeft K) := ⟨z, hz⟩
    rw [show Set.range (ProjectiveLine.overlapLeft K) =
      (PrimeSpectrum.basicOpen (Polynomial.X : K[X]) : Set (PrimeSpectrum K[X])) from
      PrimeSpectrum.localization_away_comap_range _ _] at hx
    rw [show Set.range (left S) =
      (PrimeSpectrum.basicOpen (Polynomial.X : S[X]) : Set (PrimeSpectrum S[X])) from
      PrimeSpectrum.localization_away_comap_range _ _]
    change (Polynomial.mapRingHom (algebraMap K S)) Polynomial.X ∉ x.asIdeal at hx
    change Polynomial.X ∉ x.asIdeal
    simpa using hx
  · rintro ⟨z, rfl⟩
    exact ⟨right S z, (congrArg (fun f ↦ f z) (condition K S)).symm⟩

/-- The Laurent spectrum is the actual product-chart intersection. -/
theorem isPullback : IsPullback (left S) (right S)
    (productChartMap K S false) (productChartMap K S true) :=
  (IsOpenImmersion.isPullback _ _ _ _ (condition K S) (preimage_right K S)).flip

/-- The two polynomial charts cover the full fiber product. -/
theorem covers (x : product K S) : x ∈ Set.range (productChartMap K S false) ∨
    x ∈ Set.range (productChartMap K S true) := by
  obtain ⟨b, y, hy⟩ := (productChartCover K S).exists_eq x
  cases b
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

/-- Morphisms on the product glue across the Laurent transition. -/
theorem isPushout : IsPushout (left S) (right S)
    (productChartMap K S false) (productChartMap K S true) :=
  BinaryOpenDescent.isPushout _ _ _ _ (isPullback K S) (covers K S)
end FLT.Mazur.ProjectiveLineProductOverlap
