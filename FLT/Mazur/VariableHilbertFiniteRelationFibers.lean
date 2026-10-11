/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertEtaleRelation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Finite fibers of the original full translation relation

An affine étale translation base has finite fibers over the original base.
The full test intersection embeds openly in its base change, so its fibers
are finite even when the test and the intersection are not quasi-compact.
No finiteness of the translation morphism is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) (V : Over (Spec (.of R)))
  [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- Every original full test intersection has finite fibers, including on non-affine tests. -/
theorem variableHilbertOverlapToTest_finite_fiber
    (U : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op U)) (x : U.left) :
    ((variableHilbertOverlapToTest f d V c U s).left ⁻¹' {x}).Finite := by
  let p := (prod.fst : prod U V ⟶ U).left
  let j := (variableHilbertOverlapArrow f d V c U s).left
  have hp : p = (Over.prodLeftIsoPullback U V).hom ≫ pullback.fst U.hom V.hom :=
    (Over.prodLeftIsoPullback_hom_fst U V).symm
  let _ : Etale p := by rw [hp]; infer_instance
  let _ : QuasiCompact p := by rw [hp]; infer_instance
  let _ : LocallyQuasiFinite p := by
    constructor
    intro A hA B hB h
    have hφ := p.etale_appLE hA hB h
    algebraize [(p.appLE A B h).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)
  change (j ⁻¹' (p ⁻¹' {x})).Finite
  exact (p.finite_preimage_singleton x).preimage j.injective.injOn

variable {L : X.Modules} (hL : AmpleLineBundle L)

/-- The second endpoint of the full original relation has finite fibers. -/
theorem variableChartRelationSnd_finite_fiber (x : (variableHilbertTest f d V).left) :
    ((variableChartRelationSnd f hL d V c).left ⁻¹' {x}).Finite :=
  variableHilbertOverlapToTest_finite_fiber f d V c _ _ x

/-- Symmetry gives finite fibers of the first endpoint without discarding any base maps. -/
theorem variableChartRelationFst_finite_fiber (x : (variableHilbertTest f d V).left) :
    ((variableChartRelationFst f hL d V c).left ⁻¹' {x}).Finite := by
  let e := (Over.forget _).mapIso (variableChartRelationSwapIso f hL d V c)
  have he : e.hom ≫ (variableChartRelationSnd f hL d V c).left =
      (variableChartRelationFst f hL d V c).left :=
    congrArg Over.Hom.left (variableChartEquivalenceRelation f hL d V c).symmetry₂
  rw [← he]
  change (e.hom ⁻¹' ((variableChartRelationSnd f hL d V c).left ⁻¹' {x})).Finite
  exact (variableChartRelationSnd_finite_fiber f d V c hL x).preimage
    e.hom.injective.injOn

end FLT.Mazur.HilbertChart
