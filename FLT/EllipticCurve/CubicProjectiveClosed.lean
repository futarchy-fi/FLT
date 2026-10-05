/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicProjectiveMorphism
public import FLT.Mazur.ProjectiveSpaceProper

/-!
# The Weierstrass closed immersion and proper structural morphism

The two affine cubic charts are exactly the inverse images of the Y and Z
projective opens. Together with the complement of the homogeneous cubic,
these opens cover the plane. Closed immersions descend across this target
cover; properness follows from properness of the projective plane.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FLT.Mazur.ProjectiveSpace

set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The localized overlap is precisely the nonvanishing locus of the second coordinate. -/
theorem overlapInclusion_range (b : Bool) :
    Set.range (overlapInclusion W b) =
      (PrimeSpectrum.basicOpen (coord W b 1) : Set (PrimeSpectrum (Ring W b))) :=
  PrimeSpectrum.localization_away_comap_range (Overlap W b) (coord W b 1)

/-- The preimage of Z≠0 is exactly the ordinary affine chart of the glued scheme. -/
theorem toProjective_preimage_Z :
    toProjective W ⁻¹ᵁ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) 2 =
      (affineChart W).opensRange := by
  have h₀ := chartToProjective_preimage_chart W false 2
  have h₁ := chartToProjective_preimage_chart W true 2
  have hm₀ (y : chart W false) :
      toProjective W (affineChart W y) ∈ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) 2 := by
    change (affineChart W ≫ toProjective W) y ∈ _
    rw [affineChart_toProjective]
    change y ∈ chartToProjective W false ⁻¹ᵁ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) 2
    rw [h₀]
    change y ∈ PrimeSpectrum.basicOpen (1 : Ring W false)
    simp
  ext x
  change toProjective W x ∈ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) 2 ↔
    x ∈ Set.range (affineChart W)
  constructor
  · intro hx
    rcases charts_cover W x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨y, rfl⟩
    · change (infinityChart W ≫ toProjective W) y ∈ _ at hx
      rw [infinityChart_toProjective] at hx
      change y ∈ chartToProjective W true ⁻¹ᵁ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) 2 at hx
      rw [h₁] at hx
      change y ∈ PrimeSpectrum.basicOpen (coord W true 1) at hx
      obtain ⟨z, rfl⟩ := (Set.ext_iff.mp (overlapInclusion_range W true) y).mpr hx
      refine ⟨overlapInclusion W false ((overlapIso W).inv z), ?_⟩
      have h := congrArg (fun f ↦ (overlapIso W).inv ≫ f) (overlap_condition W)
      unfold overlapRight at h
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h
      exact congrArg (fun f ↦ f z) h
  · rintro ⟨y, rfl⟩
    exact hm₀ y

/-- The preimage of Y≠0 is exactly the infinity chart of the glued scheme. -/
theorem toProjective_preimage_Y :
    toProjective W ⁻¹ᵁ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) 1 =
      (infinityChart W).opensRange := by
  have h₀ := chartToProjective_preimage_chart W false 1
  have h₁ := chartToProjective_preimage_chart W true 1
  have hm₁ (y : chart W true) :
      toProjective W (infinityChart W y) ∈ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) 1 := by
    change (infinityChart W ≫ toProjective W) y ∈ _
    rw [infinityChart_toProjective]
    change y ∈ chartToProjective W true ⁻¹ᵁ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) 1
    rw [h₁]
    change y ∈ PrimeSpectrum.basicOpen (1 : Ring W true)
    simp
  ext x
  change toProjective W x ∈ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) 1 ↔
    x ∈ Set.range (infinityChart W)
  constructor
  · intro hx
    rcases charts_cover W x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · change (affineChart W ≫ toProjective W) y ∈ _ at hx
      rw [affineChart_toProjective] at hx
      change y ∈ chartToProjective W false ⁻¹ᵁ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) 1 at hx
      rw [h₀] at hx
      change y ∈ PrimeSpectrum.basicOpen (coord W false 1) at hx
      obtain ⟨z, rfl⟩ := (Set.ext_iff.mp (overlapInclusion_range W false) y).mpr hx
      refine ⟨overlapRight W z, ?_⟩
      exact (congrArg (fun f ↦ f z) (overlap_condition W)).symm
    · exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact hm₁ y

/-- Either source chart inclusion, indexed in the same way as its ring. -/
def sourceChart (b : Bool) : chart W b ⟶ scheme W :=
  by cases b
     · exact affineChart W
     · exact infinityChart W

instance sourceChart_isOpenImmersion (b : Bool) : IsOpenImmersion (sourceChart W b) := by
  cases b <;> dsimp [sourceChart] <;> infer_instance

/-- The source chart is exactly the inverse image of its projective open. -/
theorem toProjective_preimage_pivot (b : Bool) :
    toProjective W ⁻¹ᵁ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) (pivot b) =
      (sourceChart W b).opensRange := by
  cases b
  · exact toProjective_preimage_Z W
  · exact toProjective_preimage_Y W

/-- The affine closed immersion into the matching projective open. -/
def projectiveChartMorphism (b : Bool) :
    chart W b ⟶ (FLT.Mazur.ProjectiveSpace.chart R (Fin 3) (pivot b)).toScheme :=
  Spec.map (CommRingCat.ofHom (projectiveChartRingMap W b)) ≫
    (chartIso R (Fin 3) (pivot b)).inv

instance projectiveChartMorphism_isClosedImmersion (b : Bool) :
    IsClosedImmersion (projectiveChartMorphism W b) := by
  unfold projectiveChartMorphism
  infer_instance

/-- The affine chart square is the pullback of the global morphism. -/
theorem projectiveChartIsPullback (b : Bool) :
    IsPullback (projectiveChartMorphism W b) (sourceChart W b)
      (FLT.Mazur.ProjectiveSpace.chart R (Fin 3) (pivot b)).ι (toProjective W) := by
  apply IsOpenImmersion.isPullback
  · have h : sourceChart W b ≫ toProjective W = chartToProjective W b := by
      cases b
      · exact affineChart_toProjective W
      · exact infinityChart_toProjective W
    rw [h, chartToProjective_eq]
    exact (Category.assoc _ _ _).symm
  · rw [Scheme.Opens.opensRange_ι, toProjective_preimage_pivot]

/-- Identification of a global target restriction with its affine cubic chart. -/
def projectiveRestrictIso (b : Bool) :
    chart W b ≅
      (toProjective W ⁻¹ᵁ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) (pivot b)).toScheme :=
  (projectiveChartIsPullback W b).isoIsPullback _ _
    (isPullback_morphismRestrict (toProjective W)
      (FLT.Mazur.ProjectiveSpace.chart R (Fin 3) (pivot b)))

/-- Under the comparison, the restriction is the constructed affine closed immersion. -/
@[reassoc (attr := simp)] theorem projectiveRestrictIso_hom_restrict (b : Bool) :
    (projectiveRestrictIso W b).hom ≫
      (toProjective W ∣_ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) (pivot b)) =
        projectiveChartMorphism W b :=
  (projectiveChartIsPullback W b).isoIsPullback_hom_fst _ _ _

/-- Both standard target restrictions of the global morphism are closed immersions. -/
instance toProjective_restrict_pivot_isClosedImmersion (b : Bool) :
    IsClosedImmersion
      (toProjective W ∣_ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) (pivot b)) := by
  have h : toProjective W ∣_ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) (pivot b) =
      (projectiveRestrictIso W b).inv ≫ projectiveChartMorphism W b := by
    rw [← projectiveRestrictIso_hom_restrict, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- The Weierstrass equation is homogeneous of degree three. -/
theorem projective_polynomial_homogeneous :
    W.toProjective.polynomial ∈ grading R (Fin 3) 3 := by
  have hx := MvPolynomial.isHomogeneous_X R (0 : Fin 3)
  have hy := MvPolynomial.isHomogeneous_X R (1 : Fin 3)
  have hz := MvPolynomial.isHomogeneous_X R (2 : Fin 3)
  exact (((hy.pow 2).mul hz).add (((hx.C_mul W.a₁).mul hy).mul hz) |>.add
    ((hy.C_mul W.a₃).mul (hz.pow 2))).sub
      (((hx.pow 3).add (((hx.pow 2).C_mul W.a₂).mul hz) |>.add
        ((hx.C_mul W.a₄).mul (hz.pow 2))).add ((hz.pow 3).C_mul W.a₆))

/-- The homogeneous equation vanishes in both affine quotient coordinate rings. -/
theorem eval_homogeneousCoords (b : Bool) :
    MvPolynomial.eval₂ (algebraMap R (Ring W b)) (homogeneousCoords W b)
      W.toProjective.polynomial = 0 := by
  let q := Ideal.Quotient.mk (Ideal.span {equation W b})
  let v : Fin 3 → MvPolynomial (Fin 2) R := fun i ↦
    Fin.cases 1 MvPolynomial.X ((projectiveCoordinateOrder b).symm i)
  have hm : q.comp (MvPolynomial.eval₂Hom MvPolynomial.C v) =
      MvPolynomial.eval₂Hom (algebraMap R (Ring W b)) (homogeneousCoords W b) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      rfl
    · intro i
      simp only [RingHom.comp_apply]
      calc
        q (MvPolynomial.eval₂Hom MvPolynomial.C v (MvPolynomial.X i)) =
            q (v i) := congrArg q (MvPolynomial.eval₂Hom_X' _ _ i)
        _ = homogeneousCoords W b i := by
          cases b <;> fin_cases i <;> rfl
        _ = _ := (MvPolynomial.eval₂Hom_X' _ _ i).symm
  change (MvPolynomial.eval₂Hom (algebraMap R _) (homogeneousCoords W b))
    W.toProjective.polynomial = 0
  rw [← hm]
  change q (MvPolynomial.eval₂Hom MvPolynomial.C v W.toProjective.polynomial) = 0
  rw [equation_in_projective_coordinates]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The complement of the cubic has empty preimage on each source chart. -/
theorem chartToProjective_preimage_cubic_complement (b : Bool) :
    chartToProjective W b ⁻¹ᵁ Proj.basicOpen (grading R (Fin 3)) W.toProjective.polynomial =
      ⊥ := by
  rw [chartToProjective_eq, Scheme.Hom.comp_preimage]
  change (Spec.map (CommRingCat.ofHom (projectiveChartRingMap W b))) ⁻¹ᵁ
    ((Proj.awayι (grading R (Fin 3)) (MvPolynomial.X (pivot b))
      (MvPolynomial.isHomogeneous_X R (pivot b)) (by decide)) ⁻¹ᵁ
        Proj.basicOpen (grading R (Fin 3)) W.toProjective.polynomial) = _
  rw [Proj.awayι_preimage_basicOpen (𝒜 := grading R (Fin 3))
    (MvPolynomial.isHomogeneous_X R (pivot b)) (by decide)
    (projective_polynomial_homogeneous W) (by decide), SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen (chartEval R (Fin 3) (algebraMap R _)
    (homogeneousCoords W b) (pivot b) (homogeneousCoords_pivot W b)
      (HomogeneousLocalization.Away.isLocalizationElem
        (MvPolynomial.isHomogeneous_X R (pivot b)) (projective_polynomial_homogeneous W))) = ⊥
  rw [HomogeneousLocalization.Away.isLocalizationElem, chartEval_mk]
  simp only [pow_one, eval_homogeneousCoords, PrimeSpectrum.basicOpen_zero]

/-- The global morphism factors set-theoretically through the homogeneous cubic. -/
theorem toProjective_preimage_cubic_complement :
    toProjective W ⁻¹ᵁ Proj.basicOpen (grading R (Fin 3)) W.toProjective.polynomial = ⊥ := by
  ext x
  change toProjective W x ∈ Proj.basicOpen (grading R (Fin 3)) W.toProjective.polynomial ↔ False
  constructor
  · intro hx
    rcases charts_cover W x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · change y ∈ (affineChart W ≫ toProjective W) ⁻¹ᵁ
        Proj.basicOpen (grading R (Fin 3)) W.toProjective.polynomial at hx
      rw [affineChart_toProjective, chartToProjective_preimage_cubic_complement] at hx
      exact hx
    · change y ∈ (infinityChart W ≫ toProjective W) ⁻¹ᵁ
        Proj.basicOpen (grading R (Fin 3)) W.toProjective.polynomial at hx
      rw [infinityChart_toProjective, chartToProjective_preimage_cubic_complement] at hx
      exact hx
  · exact False.elim

/-- A cover of the entire projective plane: Y≠0, Z≠0, and the complement of the cubic. -/
def projectiveTargetOpen : Option Bool → (FLT.Mazur.ProjectiveSpace.space R (Fin 3)).Opens
  | none => Proj.basicOpen (grading R (Fin 3)) W.toProjective.polynomial
  | some b => FLT.Mazur.ProjectiveSpace.chart R (Fin 3) (pivot b)

/-- The target opens cover even points outside the cubic. -/
theorem iSup_projectiveTargetOpen : ⨆ i, projectiveTargetOpen W i = ⊤ := by
  apply top_unique
  intro x _
  apply TopologicalSpace.Opens.mem_iSup.mpr
  by_cases hx : W.toProjective.polynomial ∈ x.asHomogeneousIdeal.toIdeal
  · rcases projective_locus_two_chart_cover W x hx with hy | hz
    · exact ⟨some true, hy⟩
    · exact ⟨some false, hz⟩
  · exact ⟨none, hx⟩

/-- The constructed global morphism is a closed immersion into the projective plane. -/
instance toProjective_isClosedImmersion : IsClosedImmersion (toProjective W) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (projectiveTargetOpen W) (iSup_projectiveTargetOpen W)
  intro i
  cases i with
  | none =>
    have : IsEmpty
        ((toProjective W ⁻¹ᵁ Proj.basicOpen (grading R (Fin 3))
          W.toProjective.polynomial).toScheme) := by
      rw [toProjective_preimage_cubic_complement]
      exact ⟨fun x ↦ x.2⟩
    change IsClosedImmersion (toProjective W ∣_
      Proj.basicOpen (grading R (Fin 3)) W.toProjective.polynomial)
    infer_instance
  | some b => exact toProjective_restrict_pivot_isClosedImmersion W b

/-- The glued Weierstrass scheme is proper over every commutative coefficient ring. -/
instance toBase_isProper : IsProper (toBase W) := by
  rw [← toProjective_baseProjection]
  infer_instance

end WeierstrassCurve.CubicCharts
