/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicBaseChange
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Global base change and geometric connectedness

The coefficient morphism has a cartesian square on the two-chart cover.
Descending this property gives global base change, and the integral field
models then prove geometric connectedness. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (S : Type u) [CommRing S] [Algebra R S]

@[reassoc (attr := simp)] theorem sourceChart_coefficientMorphism (b : Bool) :
    sourceChart (W.map (algebraMap R S)) b ≫ coefficientMorphism W S =
      chartCoefficientMorphism W S b ≫ sourceChart W b := by
  cases b
  · exact affineChart_coefficientMorphism W S
  · exact infinityChart_coefficientMorphism W S

/-- The opposite chart meets a chart in the principal overlap open. -/
theorem sourceChart_preimage_opposite (b : Bool) :
    sourceChart W b ⁻¹ᵁ (sourceChart W (!b)).opensRange =
      PrimeSpectrum.basicOpen (coord W b 1) := by
  rw [← toProjective_preimage_pivot]
  change (sourceChart W b ≫ toProjective W) ⁻¹ᵁ
    FLT.Mazur.ProjectiveSpace.chart R (Fin 3) (pivot (!b)) = _
  have h : sourceChart W b ≫ toProjective W = chartToProjective W b := by
    cases b
    · exact affineChart_toProjective W
    · exact infinityChart_toProjective W
  rw [h, chartToProjective_preimage_chart]
  cases b <;> rfl

/-- Coefficient extension preserves the principal overlap open. -/
theorem chartCoefficientMorphism_preimage_overlap (b : Bool) :
    chartCoefficientMorphism W S b ⁻¹ᵁ PrimeSpectrum.basicOpen (coord W b 1) =
      PrimeSpectrum.basicOpen (coord (W.map (algebraMap R S)) b 1) := by
  ext x
  change chartCoefficientMap W S b (coord W b 1) ∉ x.asIdeal ↔
    coord (W.map (algebraMap R S)) b 1 ∉ x.asIdeal
  rw [chartCoefficientMap_coord]

/-- A chart pulls back to exactly the matching chart under coefficient extension. -/
theorem coefficientMorphism_preimage_sourceChart (b : Bool) :
    coefficientMorphism W S ⁻¹ᵁ (sourceChart W b).opensRange =
      (sourceChart (W.map (algebraMap R S)) b).opensRange := by
  have hlocal (c : Bool) :
      sourceChart (W.map (algebraMap R S)) c ⁻¹ᵁ
          (coefficientMorphism W S ⁻¹ᵁ (sourceChart W b).opensRange) =
        sourceChart (W.map (algebraMap R S)) c ⁻¹ᵁ
          (sourceChart (W.map (algebraMap R S)) b).opensRange := by
    rw [← Scheme.Hom.comp_preimage, sourceChart_coefficientMorphism,
      Scheme.Hom.comp_preimage]
    by_cases h : b = c
    · subst b
      simp
    · have hb : b = !c := by cases b <;> cases c <;> simp_all
      subst b
      rw [sourceChart_preimage_opposite, sourceChart_preimage_opposite,
        chartCoefficientMorphism_preimage_overlap]
  ext x
  rcases charts_cover (W.map (algebraMap R S)) x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact Iff.of_eq (congrArg (fun U ↦ y ∈ U) (hlocal false))
  · exact Iff.of_eq (congrArg (fun U ↦ y ∈ U) (hlocal true))

/-- Restriction of the global coefficient morphism is the coefficient map of a chart. -/
theorem coefficientChart_isPullback (b : Bool) :
    IsPullback (chartCoefficientMorphism W S b)
      (sourceChart (W.map (algebraMap R S)) b) (sourceChart W b)
      (coefficientMorphism W S) := by
  apply IsOpenImmersion.isPullback
  · exact sourceChart_coefficientMorphism W S b
  · exact coefficientMorphism_preimage_sourceChart W S b

@[reassoc (attr := simp)] theorem sourceChart_toBase (b : Bool) :
    sourceChart W b ≫ toBase W = chartToBase W b := by
  cases b
  · exact affineChart_toBase W
  · exact infinityChart_toBase W

/-- The global coefficient square is cartesian. -/
theorem coefficientMorphism_isPullback :
    IsPullback (coefficientMorphism W S) (toBase (W.map (algebraMap R S)))
      (toBase W) (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (sourceOpenCover W)
  intro b
  let h := coefficientChart_isPullback W S b
  let h' := (IsPullback.of_hasPullback (coefficientMorphism W S) (sourceChart W b)).flip
  let e := h.isoIsPullback _ _ h'
  refine (chartBaseChange_isPullback W S b).of_iso e
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ (by simp)
  · simp only [Iso.refl_hom, Category.comp_id]
    change chartCoefficientMorphism W S b = e.hom ≫ pullback.snd _ _
    exact (h.isoIsPullback_hom_fst _ _ h').symm
  · simp only [Iso.refl_hom, Category.comp_id]
    change chartToBase (W.map (algebraMap R S)) b =
      e.hom ≫ pullback.fst _ _ ≫ toBase (W.map (algebraMap R S))
    rw [← Category.assoc, h.isoIsPullback_hom_snd _ _ h', sourceChart_toBase]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact (sourceChart_toBase W b).symm

/-- The glued cubic with extended coefficients is the base-changed cubic. -/
def baseChangeIso : scheme (W.map (algebraMap R S)) ≅
    pullback (toBase W) (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (coefficientMorphism_isPullback W S).isoPullback

@[reassoc (attr := simp)] theorem baseChangeIso_hom_fst :
    (baseChangeIso W S).hom ≫ pullback.fst _ _ = coefficientMorphism W S :=
  (coefficientMorphism_isPullback W S).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem baseChangeIso_hom_snd :
    (baseChangeIso W S).hom ≫ pullback.snd _ _ = toBase (W.map (algebraMap R S)) :=
  (coefficientMorphism_isPullback W S).isoPullback_hom_snd

/-- Every geometric fiber of the glued Weierstrass cubic is connected. -/
instance toBase_geometricallyConnected : GeometricallyConnected (toBase W) := by
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun X : Scheme.{u} ↦ ConnectedSpace X) (R := R) (f := toBase W)).mpr
  intro K _ _
  rw [← (baseChangeIso W K).hom.homeomorph.connectedSpace_iff]
  infer_instance

end WeierstrassCurve.CubicCharts
