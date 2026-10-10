/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineRelativeTangent
public import FLT.Mazur.WeierstrassProjectivePointSmooth

/-!
# Relative smoothness is residue-field nonsingularity in the affine chart

Vertical tangent obstructions rule out every singular residue point. Conversely,
a nonsingular point lies in a free derivative open. Both directions hold over
arbitrary coefficient rings and in every residue characteristic.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

open PolygonNodePresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
  (p : PrimeSpectrum (Coordinate W 2))

/-- Every relatively smooth affine point is nonsingular over its actual residue field. -/
theorem affineRelativeSmooth_nonsingular
    (hp : p ∈ (chartStructure W 2).smoothLocus) :
    (W.map (algebraMap R p.asIdeal.ResidueField)).toAffine.Nonsingular
      (algebraMap (Coordinate W 2) p.asIdeal.ResidueField (coord W 2 0))
      (algebraMap (Coordinate W 2) p.asIdeal.ResidueField (coord W 2 1)) := by
  let _ : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W 2)))) :=
    inferInstanceAs (LocallyOfFinitePresentation (chartStructure W 2))
  let e : Coordinate W 2 →ₐ[R] p.asIdeal.ResidueField := IsScalarTower.toAlgHom R _ _
  apply (Affine.nonsingular_iff' _ _).mpr
  refine ⟨affine_equation_of_hom W e, ?_⟩
  by_contra! h
  obtain ⟨hx, hy⟩ := h
  exact relativeJet_origin_not_formallySmooth p.asIdeal e (affineRelativeTangent W e hy)
    (Ideal.ker_algebraMap_residueField p.asIdeal) (affineRelativeTangent_origin W e hy)
    (affineRelativeTangent_no_lift W e hy hx) (spec_smooth_implies_algebra p hp)

/-- Conversely, a nonsingular affine residue point belongs to the relative smooth locus. -/
theorem affineRelativeSmooth_of_nonsingular
    (hn : (W.map (algebraMap R p.asIdeal.ResidueField)).toAffine.Nonsingular
      (algebraMap (Coordinate W 2) p.asIdeal.ResidueField (coord W 2 0))
      (algebraMap (Coordinate W 2) p.asIdeal.ResidueField (coord W 2 1))) :
    p ∈ (chartStructure W 2).smoothLocus := by
  let e : Coordinate W 2 →ₐ[R] p.asIdeal.ResidueField := IsScalarTower.toAlgHom R _ _
  have hv : (W.map (algebraMap R p.asIdeal.ResidueField)).toProjective.Nonsingular
      (e ∘ coord W 2) := by
    have he : e ∘ coord W 2 = ![e (coord W 2 0), e (coord W 2 1), 1] := by
      funext i
      fin_cases i <;> simp
    rw [he]
    exact (Projective.nonsingular_some _ _).mpr hn
  obtain ⟨i, hij, hi⟩ := normalized_free_partial_exists _ 2 _ hv (by simp)
  have hm : chartPartial W 2 i ∉ p.asIdeal := by
    intro h
    apply hi
    rw [← chartPartial_map W 2 i e]
    exact Ideal.algebraMap_residueField_eq_zero.mpr h
  apply chartPartial_range_smooth W 2 i hij
  rw [PrincipalAffineRefinement.range_inclusion]
  exact hm

/-- The actual relative affine smooth locus has precisely the classical residue-field test. -/
theorem affineRelativeSmooth_iff_nonsingular :
    p ∈ (chartStructure W 2).smoothLocus ↔
      (W.map (algebraMap R p.asIdeal.ResidueField)).toAffine.Nonsingular
        (algebraMap (Coordinate W 2) p.asIdeal.ResidueField (coord W 2 0))
        (algebraMap (Coordinate W 2) p.asIdeal.ResidueField (coord W 2 1)) :=
  ⟨affineRelativeSmooth_nonsingular W p, affineRelativeSmooth_of_nonsingular W p⟩

/-- A field-valued affine point in the relative smooth open is classically nonsingular. -/
theorem affineFieldPoint_nonsingular_of_smooth {K : Type u} [Field K] [Algebra R K]
    (e : Coordinate W 2 →ₐ[R] K)
    (hs : Set.range (Spec.map (CommRingCat.ofHom e.toRingHom)) ⊆
      (chartStructure W 2).smoothLocus) :
    (W.map (algebraMap R K)).toAffine.Nonsingular (e (coord W 2 0)) (e (coord W 2 1)) := by
  let _ : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W 2)))) :=
    inferInstanceAs (LocallyOfFinitePresentation (chartStructure W 2))
  let q : PrimeSpectrum (Coordinate W 2) :=
    PrimeSpectrum.comap e.toRingHom ⟨⊥, inferInstance⟩
  have hq : q ∈ (chartStructure W 2).smoothLocus := hs ⟨⟨⊥, inferInstance⟩, rfl⟩
  apply (Affine.nonsingular_iff' _ _).mpr
  refine ⟨affine_equation_of_hom W e, ?_⟩
  by_contra! h
  obtain ⟨hx, hy⟩ := h
  exact relativeJet_origin_not_formallySmooth q.asIdeal e (affineRelativeTangent W e hy)
    rfl (affineRelativeTangent_origin W e hy) (affineRelativeTangent_no_lift W e hy hx)
    (spec_smooth_implies_algebra q hq)

end FLT.Mazur.WeierstrassIntegralChart
