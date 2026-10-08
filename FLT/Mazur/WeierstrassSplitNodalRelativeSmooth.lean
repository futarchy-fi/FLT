/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalRelativeTangent
public import FLT.Mazur.WeierstrassSplitNodalFieldSmooth

/-!
# The entire relative smooth locus of the split nodal integral cubic

At every prime omitted by the Y chart, the residue-field vertical tangent
obstructs smoothness over the original base. Hence the original torus chart
is the full relative smooth locus over every commutative coefficient ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial

namespace FLT.Mazur.WeierstrassIntegralChart

open PolygonNodePresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (a : Rˣ)

/-- A relative smooth point in the finite chart has nonvanishing Y coordinate. -/
theorem splitNodalRelativeAffine_smooth_y (p : chartScheme (splitNodalEquation a) 2)
    (hp : p ∈ (chartStructure (splitNodalEquation a) 2).smoothLocus) :
    coord (splitNodalEquation a) 2 1 ∉ p.asIdeal := by
  intro hy
  let _ : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate (splitNodalEquation a) 2)))) :=
    inferInstanceAs (LocallyOfFinitePresentation (chartStructure (splitNodalEquation a) 2))
  have hx : coord (splitNodalEquation a) 2 0 ∈ p.asIdeal := by
    apply p.isPrime.mem_of_pow_mem 3
    rw [← sub_eq_zero.mp (splitNodalRelativeAffine_relation a)]
    exact p.asIdeal.add_mem (p.asIdeal.pow_mem_of_mem hy 2 (by omega))
      (p.asIdeal.mul_mem_left _ hy)
  let K := p.asIdeal.ResidueField
  let e : Coordinate (splitNodalEquation a) 2 →ₐ[R] K :=
    IsScalarTower.toAlgHom R _ K
  apply relativeJet_origin_not_formallySmooth p.asIdeal e
    (splitNodalRelativeTangent (K := K) a) (Ideal.ker_algebraMap_residueField p.asIdeal) ?_
    (splitNodalRelativeTangent_no_lift a) (spec_smooth_implies_algebra p hp)
  apply hom_ext (S := K)
  intro i
  fin_cases i
  · simpa [AlgHom.comp_apply, e] using
      (Ideal.algebraMap_residueField_eq_zero.mpr hx).symm
  · simpa [AlgHom.comp_apply, e] using
      (Ideal.algebraMap_residueField_eq_zero.mpr hy).symm
  · simp [AlgHom.comp_apply, e]

/-- The Y chart is the full relative smooth locus, over every coefficient ring. -/
theorem splitNodalRelative_smooth_range :
    (integralSmoothOpen (splitNodalEquation a) : Set (integralCurve (splitNodalEquation a))) =
      Set.range (integralCurveChart (splitNodalEquation a) 1) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases integralCurve_yz_cover (splitNodalEquation a) x with hy | ⟨z, rfl⟩
    · exact hy
    · apply integralCurveChart_mem_range (splitNodalEquation a) 2 1 z
      apply splitNodalRelativeAffine_smooth_y a z
      exact (integralCurveChart_preimage_smooth (splitNodalEquation a) 2).le hx
  · exact splitNodalChart_range_smooth a

/-- The actual torus map is surjective onto the entire relative smooth locus. -/
theorem splitNodalRelative_torusToSmooth_surjective :
    Function.Surjective (splitNodalTorusToSmooth a) := by
  intro x
  obtain ⟨y, hy⟩ := (splitNodalRelative_smooth_range a).le x.property
  obtain ⟨z, rfl⟩ := (splitNodalTorusIso a).hom.surjective y
  refine ⟨z, ?_⟩
  apply (integralSmoothOpen (splitNodalEquation a)).ι.isOpenEmbedding.injective
  change (splitNodalTorusToSmooth a ≫ (integralSmoothOpen (splitNodalEquation a)).ι) z = _
  rw [splitNodalTorusToSmooth_inclusion]
  exact hy

/-- The open immersion from the torus is an isomorphism onto the full relative smooth locus. -/
instance splitNodalRelative_torusToSmooth_isIso : IsIso (splitNodalTorusToSmooth a) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply TopologicalSpace.Opens.ext
  exact (splitNodalRelative_torusToSmooth_surjective a).range_eq

/-- The relative smooth locus of the original nodal integral cubic is the original torus. -/
def splitNodalRelativeSmoothIso : Spec (.of R[T;T⁻¹]) ≅
    (integralSmoothOpen (splitNodalEquation a)).toScheme :=
  asIso (splitNodalTorusToSmooth a)

/-- The full smooth-locus comparison preserves the original coefficient morphism. -/
@[reassoc] theorem splitNodalRelativeSmoothIso_structure :
    (splitNodalRelativeSmoothIso a).hom ≫ integralSmoothStructure (splitNodalEquation a) =
      (MultiplicativeGroupScheme.gm R).hom := by
  change splitNodalTorusToSmooth a ≫
    (integralSmoothOpen (splitNodalEquation a)).ι ≫ integralCurveStructure _ = _
  rw [splitNodalTorusToSmooth_inclusion_assoc]
  exact (Category.assoc _ _ _).trans
    ((congrArg ((splitNodalTorusIso a).hom ≫ ·)
      (integralCurveChart_structure (splitNodalEquation a) 1)).trans
        (splitNodalTorusIso_structure a))

/-- The entire relative smooth open is isomorphic to the multiplicative group over the base. -/
def splitNodalRelativeSmoothOverIso : MultiplicativeGroupScheme.gm R ≅
    Over.mk (integralSmoothStructure (splitNodalEquation a)) :=
  Over.isoMk (splitNodalRelativeSmoothIso a) (splitNodalRelativeSmoothIso_structure a)

end FLT.Mazur.WeierstrassIntegralChart
