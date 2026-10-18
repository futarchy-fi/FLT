/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassProjectiveSmoothResidues

/-!
# Relative dimension one on the entire smooth Weierstrass open

At every point of the relative smooth locus, a free partial derivative is
nonzero in the residue field. The corresponding standard smooth derivative
charts cover the whole smooth open, even when the discriminant is not a unit.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- Every smooth chart point is in a free-derivative localization. -/
theorem smoothChart_partial_exists (j : Fin 3) (p : PrimeSpectrum (Coordinate W j))
    (hp : integralCurveChart W j p ∈ integralSmoothOpen W) :
    ∃ i : Fin 3, i ≠ j ∧ chartPartial W j i ∉ p.asIdeal := by
  let f : Coordinate W j →ₐ[R] p.asIdeal.ResidueField :=
    IsScalarTower.toAlgHom R (Coordinate W j) p.asIdeal.ResidueField
  have hn := chartAlgebra_residue_nonsingular_at W j (AlgHom.id R (Coordinate W j)) p
    (by simpa using hp)
  obtain ⟨i, hij, hi⟩ := normalized_free_partial_exists
    (W.map (algebraMap R p.asIdeal.ResidueField)) j (f ∘ coord W j) hn (by simp)
  refine ⟨i, hij, ?_⟩
  intro hm
  apply hi
  rw [← chartPartial_map W j i f]
  exact Ideal.algebraMap_residueField_eq_zero.mpr hm

/-- The actual standard smooth derivative charts cover the full relative smooth open. -/
def integralSmoothDerivativeCover : (integralSmoothOpen W).toScheme.OpenCover where
  I₀ := {a : Fin 3 × Fin 3 // a.2 ≠ a.1}
  X a := Spec (.of (Localization.Away (chartPartial W a.val.1 a.val.2)))
  f a := chartPartialToSmooth W a.val.1 a.val.2 a.property
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun _ ↦ inferInstance⟩
    intro x
    obtain ⟨j, p, hp⟩ := (integralCurveOpenCover W).exists_eq x.val
    have hx : integralCurveChart W j.down p ∈ integralSmoothOpen W := by
      rw [show integralCurveChart W j.down p = x.val from hp]
      exact x.property
    obtain ⟨i, hij, hi⟩ := smoothChart_partial_exists W j.down p hx
    have hr : p ∈ Set.range (PrincipalAffineRefinement.inclusion
        (chartPartial W j.down i)) := by
      rw [PrincipalAffineRefinement.range_inclusion]
      exact hi
    obtain ⟨q, hq⟩ := hr
    refine ⟨⟨(j.down, i), hij⟩, q, ?_⟩
    apply Subtype.ext
    change (integralSmoothOpen W).ι (chartPartialToSmooth W j.down i hij q) = x.val
    have hc := congrArg (fun k ↦ k q) (chartPartialToSmooth_inclusion W j.down i hij)
    exact hc.trans ((congrArg (integralCurveChart W j.down) hq).trans hp)

/-- The full relative smooth locus has relative dimension one in every reduction type. -/
theorem integralSmoothStructure_relativeDimension :
    SmoothOfRelativeDimension 1 (integralSmoothStructure W) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (integralSmoothDerivativeCover W)).mpr
  intro a
  change SmoothOfRelativeDimension 1
    (chartPartialToSmooth W a.val.1 a.val.2 a.property ≫
      (integralSmoothOpen W).ι ≫ integralCurveStructure W)
  rw [chartPartialToSmooth_inclusion_assoc, integralCurveChart_structure]
  exact chartPartial_structure_smooth_dimension W a.val.1 a.val.2 a.property

end FLT.Mazur.WeierstrassIntegralChart
