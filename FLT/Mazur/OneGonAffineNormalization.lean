/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAffineNormalizationCoordinates
public import FLT.Mazur.OneGonCocone
public import FLT.Mazur.OneGonPinchingDescent

/-!
# The affine normalization chart in the specified projective line

Glue the reverse coordinates and compare them with the existing normalization.
The full Laurent chart remains present, including its point with coordinate one.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open scoped LaurentPolynomial
universe u
namespace FLT.Mazur.OneGonAffineNormalization
open OneGonTransition OneGonAffineCover OneGonNormalizationCoordinates
open OneGonAffineNormalizationCoordinates OneGonNormalization PinchingAffineDescent
variable (K : Type u) [Field K]

/-- Compatibility in the specified projective line. -/
theorem condition : toLaurent K ≫ rightChart K ≫ ProjectiveLine.right K =
    toOne K ≫ leftChart K ≫ ProjectiveLine.left K := by
  rw [toLaurent_rightChart_assoc, toOne_leftChart_assoc, ProjectiveLine.overlap_condition]

/-- The normalization chart obtained by deleting z=1. -/
def alpha : ProjectiveLine.chart K ⟶ ProjectiveLine.scheme K :=
  (OneGonAffineCover.isPushout K).desc (rightChart K ≫ ProjectiveLine.right K)
    (leftChart K ≫ ProjectiveLine.left K) (condition K)

@[reassoc (attr := simp)]
theorem openOne_alpha : openOne K ≫ alpha K = leftChart K ≫ ProjectiveLine.left K :=
  (OneGonAffineCover.isPushout K).inr_desc _ _ _

@[reassoc (attr := simp)]
theorem overlapLeft_alpha : ProjectiveLine.overlapLeft K ≫ alpha K =
    rightChart K ≫ ProjectiveLine.right K := (OneGonAffineCover.isPushout K).inl_desc _ _ _

@[reassoc]
theorem puncture_alpha : punctureOpen K ≫ alpha K =
    toTorus K ≫ ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K := by
  rw [← toOne_openOne, Category.assoc, openOne_alpha, toOne_leftChart_assoc]

@[reassoc (attr := simp)]
theorem zero_alpha : ProjectiveLine.chartZero K ≫ alpha K = ProjectiveLine.zero K := by
  rw [← zeroLift_openOne, Category.assoc, openOne_alpha, ← Category.assoc]
  suffices zeroLift K ≫ leftChart K = ProjectiveLine.chartZero K by
    rw [this]; rfl
  rw [leftChart_eq, zeroLift, ← Spec.map_comp, ProjectiveLine.chartZero]
  congr 1
  apply CommRingCat.hom_ext
  exact (evalZero_aeval K _).trans (congrArg evalRingHom (evalZero_leftCoordinate K))

/-- The affine endpoint one lifted to D(t). -/
def oneLift : Spec (.of K) ⟶ ProjectiveLine.overlap K :=
  Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := K) (1 : Kˣ)).toRingHom)

@[reassoc]
theorem oneLift_overlapLeft : oneLift K ≫ ProjectiveLine.overlapLeft K = chartOne K := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext <;> simp [LaurentUnitPoints.evalUnit]

@[reassoc (attr := simp)]
theorem one_alpha : chartOne K ≫ alpha K = ProjectiveLine.infinity K := by
  rw [← oneLift_overlapLeft, Category.assoc, overlapLeft_alpha, ← Category.assoc]
  suffices oneLift K ≫ rightChart K = ProjectiveLine.chartZero K by
    rw [this]; rfl
  rw [rightChart_eq, oneLift, ← Spec.map_comp, ProjectiveLine.chartZero]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext <;> simp [LaurentUnitPoints.evalUnit]

@[reassoc]
theorem leftIso_leftPatch : (leftIso K).hom ≫ leftPatch K = openOne K ≫ oneBranch K := by
  have h : (leftChange K).toRingHom.comp (aeval (leftCoordinate K)).toRingHom =
      algebraMap K[X] (awayOne K) := by
    apply Polynomial.ringHom_ext
    · intro r
      change leftChange K (aeval _ (C r)) = _
      rw [aeval_C, AlgHom.commutes]
      rfl
    · exact (congrArg (leftChange K) (aeval_X (leftCoordinate K))).trans
        (leftChange_leftCoordinate K)
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg (fun f : K[X] →+* awayOne K ↦
    f.comp (PolygonNodePresentation.B (R := K)).val.toRingHom) h

@[reassoc]
theorem rightIso_rightPatch : (rightIso K).hom ≫ rightPatch K =
    ProjectiveLine.overlapLeft K ≫ oneBranch K := by
  have h : (rightChange K).toRingHom.comp (aeval (rightCoordinate K)).toRingHom =
      (Polynomial.toLaurent : K[X] →+* K[T;T⁻¹]) := by
    apply Polynomial.ringHom_ext
    · intro r
      change rightChange K (aeval _ (C r)) = _
      rw [aeval_C, AlgHom.commutes, Polynomial.toLaurent_C]
      rfl
    · simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, aeval_X, Polynomial.toLaurent_X] using rightChange_rightCoordinate K
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg (fun f : K[X] →+* K[T;T⁻¹] ↦
    f.comp (PolygonNodePresentation.B (R := K)).val.toRingHom) h

/-- Exact comparison with the already specified projective normalization. -/
@[reassoc]
theorem alpha_normalization : alpha K ≫ normalization K = oneBranch K ≫ OneGonGluing.node K := by
  apply (OneGonAffineCover.isPushout K).hom_ext
  · simp [rightChart, rightIso_rightPatch_assoc]
  · simp [leftChart, leftIso_leftPatch_assoc]

/-- These two opens cover the projective line, including z=1. -/
theorem covers (x : ProjectiveLine.scheme K) :
    x ∈ Set.range (alpha K) ∨
      x ∈ Set.range (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) := by
  rcases ProjectiveLine.charts_cover K x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · rcases OneGonAffineCover.covers K y with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact Or.inr ⟨z, rfl⟩
    · refine Or.inl ⟨openOne K ((leftIso K).inv z), ?_⟩
      change (openOne K ≫ alpha K) _ = _
      rw [openOne_alpha]
      change ((leftIso K).inv ≫ (leftIso K).hom ≫ openOne K ≫ ProjectiveLine.left K) z = _
      simp
  · rcases OneGonAffineCover.covers K y with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · refine Or.inr ⟨(ProjectiveLine.inversion K).inv z, ?_⟩
      rw [ProjectiveLine.overlap_condition]
      change ((ProjectiveLine.inversion K).inv ≫ (ProjectiveLine.inversion K).hom ≫
        ProjectiveLine.overlapLeft K ≫ ProjectiveLine.right K) z = _
      simp only [Iso.inv_hom_id_assoc]
      rfl
    · refine Or.inl ⟨ProjectiveLine.overlapLeft K ((rightIso K).inv z), ?_⟩
      change (ProjectiveLine.overlapLeft K ≫ alpha K) _ = _
      rw [overlapLeft_alpha]
      change ((rightIso K).inv ≫ (rightIso K).hom ≫ openOne K ≫ ProjectiveLine.right K) z = _
      simp

/-- Equality across the two new charts already holds in the affine source. -/
theorem cross_eq (x : Spec (.of (awayOne K))) (y : ProjectiveLine.overlap K)
    (h : (leftChart K ≫ ProjectiveLine.left K) x =
      (rightChart K ≫ ProjectiveLine.right K) y) :
    openOne K x = ProjectiveLine.overlapLeft K y := by
  have hx : leftChart K x ∈ Set.range (ProjectiveLine.overlapLeft K) := by
    obtain ⟨i, fi, fj, z, hz, _⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (span (ProjectiveLine.overlapLeft K) (ProjectiveLine.overlapRight K))).mp h
    cases i with
    | none => cases fi; exact ⟨z, hz⟩
    | some i => cases i with
      | left => cases fj
      | right => cases fi
  have hr : Set.range (ProjectiveLine.overlapLeft K) =
      (PrimeSpectrum.basicOpen (X : K[X]) : Set (PrimeSpectrum K[X])) :=
    PrimeSpectrum.localization_away_comap_range K[T;T⁻¹] X
  rw [hr, leftChart_eq] at hx
  change aeval (leftCoordinate K) X ∉ x.asIdeal at hx
  rw [aeval_X] at hx
  have ho : openOne K x ∈ Set.range (ProjectiveLine.overlapLeft K) := by
    rw [hr]
    change algebraMap K[X] (awayOne K) X ∉ x.asIdeal
    intro hm
    exact hx (x.asIdeal.mul_mem_right (↑(denominator K)⁻¹ : awayOne K) hm)
  obtain ⟨z, hz⟩ := ho
  have he : (rightChart K ≫ ProjectiveLine.right K) z =
      (rightChart K ≫ ProjectiveLine.right K) y := by
    rw [← overlapLeft_alpha]
    change alpha K (ProjectiveLine.overlapLeft K z) = _
    rw [hz]
    exact ((congrArg (fun f ↦ f x) (openOne_alpha K)).trans h).trans
      (congrArg (fun f ↦ f y) (overlapLeft_alpha K)).symm
  exact hz.symm.trans (congrArg (ProjectiveLine.overlapLeft K)
    ((rightChart K ≫ ProjectiveLine.right K).isOpenEmbedding.injective he))

/-- The two reverse charts do not introduce additional identifications. -/
theorem alpha_injective : Function.Injective (alpha K) := by
  intro x y h
  rcases OneGonAffineCover.covers K x with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
    rcases OneGonAffineCover.covers K y with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · have he : (rightChart K ≫ ProjectiveLine.right K) x =
        (rightChart K ≫ ProjectiveLine.right K) y := by
      simpa only [← Scheme.Hom.comp_apply, overlapLeft_alpha] using h
    exact congrArg _ ((rightChart K ≫ ProjectiveLine.right K).isOpenEmbedding.injective he)
  · apply (cross_eq K y x _).symm
    simpa only [← Scheme.Hom.comp_apply, openOne_alpha, overlapLeft_alpha] using h.symm
  · apply cross_eq K x y
    simpa only [← Scheme.Hom.comp_apply, openOne_alpha, overlapLeft_alpha] using h
  · have he : (leftChart K ≫ ProjectiveLine.left K) x =
        (leftChart K ≫ ProjectiveLine.left K) y := by
      simpa only [← Scheme.Hom.comp_apply, openOne_alpha] using h
    exact congrArg _ ((leftChart K ≫ ProjectiveLine.left K).isOpenEmbedding.injective he)

instance : IsOpenImmersion (alpha K) := by
  apply IsOpenImmersion.of_openCover_source _
    (BinaryOpenDescent.cover (ProjectiveLine.overlapLeft K) (openOne K)
      (OneGonAffineCover.covers K)) (alpha_injective K)
  intro i
  cases i
  · change IsOpenImmersion (ProjectiveLine.overlapLeft K ≫ alpha K)
    rw [overlapLeft_alpha]; infer_instance
  · change IsOpenImmersion (openOne K ≫ alpha K)
    rw [openOne_alpha]; infer_instance

end FLT.Mazur.OneGonAffineNormalization
