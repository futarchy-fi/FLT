/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedSectionLine
public import FLT.Mazur.ProjectiveUnitChartPoint

/-!
# The section-line universal property on an affine projective chart

Actual affine test-scheme morphisms into a fixed standard chart, over the
specified coefficient map, classify submodules whose selected coordinate
projection is invertible. The equivalence recovers each generator by pulling
back the genuine homogeneous coordinate ratios.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R] (ι : Type u)
variable {S : Type u} [CommRing S]

/-- Actual morphisms into the affine chart over a specified coefficient morphism. -/
abbrev AffineChartPoint (f : R →+* S) (i : ι) :=
  {p : Spec (.of S) ⟶ Spec (.of (chartRing R ι i)) //
    p ≫ Spec.map (CommRingCat.ofHom (chartScalars R ι i)) = Spec.map (CommRingCat.ofHom f)}

/-- The spectrum equivalence with the actual coefficient condition retained. -/
def chartRingPointEquiv (f : R →+* S) (i : ι) :
    {g : chartRing R ι i →+* S // ∀ r, g (chartScalars R ι i r) = f r} ≃
      AffineChartPoint R ι f i where
  toFun g := ⟨Spec.map (CommRingCat.ofHom g.val), by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext g.property)⟩
  invFun p := ⟨(Spec.preimage p.val).hom, by
    intro r
    have h : Spec.map (CommRingCat.ofHom (chartScalars R ι i) ≫
        Spec.preimage p.val) = Spec.map (CommRingCat.ofHom f) := by
      rw [Spec.map_comp, Spec.map_preimage]
      exact p.property
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective h)) r⟩
  left_inv g := by
    apply Subtype.ext
    exact congrArg CommRingCat.Hom.hom (Spec.preimage_map (CommRingCat.ofHom g.val))
  right_inv p := Subtype.ext (Spec.map_preimage p.val)

/-- A standard chart classifies normalized actual section submodules. -/
def sectionLineChartEquiv (f : R →+* S) (i : ι) :
    AffineChartPoint R ι f i ≃ NormalizedSectionLine.Chart S ι i :=
  (chartRingPointEquiv R ι f i).symm.trans
    ((normalizedChartEquiv R ι f i).symm.trans (NormalizedSectionLine.tupleEquiv S ι i))

/-- The classified submodule generator consists of the pulled-back coordinate ratios. -/
lemma sectionLineChartEquiv_generator (f : R →+* S) (i : ι)
    (p : AffineChartPoint R ι f i) (j : ι) :
    NormalizedSectionLine.generator S ι i (sectionLineChartEquiv R ι f i p) j =
      (Spec.preimage p.val).hom (coordinate R ι i j) := by
  change NormalizedSectionLine.generator S ι i
    (NormalizedSectionLine.ofTuple S ι i
      (fun k ↦ (Spec.preimage p.val).hom (coordinate R ι i k)) (by simp)) j = _
  rw [NormalizedSectionLine.generator_ofTuple]

/-- A section line in a coordinate chart gives an actual projective scheme point. -/
def sectionLinePoint (f : R →+* S) (i : ι) (L : NormalizedSectionLine.Chart S ι i) :
    Spec (.of S) ⟶ space R ι :=
  ((sectionLineChartEquiv R ι f i).symm L).val ≫ chartMap R ι i

/-- The line point is computed by its unique normalized generator. -/
lemma sectionLinePoint_eq_unitChartPoint (f : R →+* S) (i : ι)
    (L : NormalizedSectionLine.Chart S ι i) :
    sectionLinePoint R ι f i L =
      unitChartPoint R ι f (NormalizedSectionLine.generator S ι i L) i 1
        (NormalizedSectionLine.generator_coordinate S ι i L) := by
  have h : chartEval R ι f (NormalizedSectionLine.generator S ι i L) i
      (NormalizedSectionLine.generator_coordinate S ι i L) =
      unitChartEval R ι f (NormalizedSectionLine.generator S ι i L) i 1
        (NormalizedSectionLine.generator_coordinate S ι i L) := by
    apply chartRing_hom_ext R ι i
    · intro r
      simp only [chartEval_scalar, unitChartEval_scalar]
    · intro j
      simp only [chartEval_coordinate, unitChartEval_coordinate, inv_one, Units.val_one, one_mul]
  change Spec.map (CommRingCat.ofHom
    (chartEval R ι f (NormalizedSectionLine.generator S ι i L) i
      (NormalizedSectionLine.generator_coordinate S ι i L))) ≫ _ = _
  rw [h]
  rfl

/-- In a fixed chart the scheme point uniquely determines the actual submodule. -/
lemma sectionLinePoint_injective (f : R →+* S) (i : ι) :
    Function.Injective (sectionLinePoint R ι f i) := by
  intro L M h
  apply (sectionLineChartEquiv R ι f i).symm.injective
  apply Subtype.ext
  exact (cancel_mono (chartMap R ι i)).mp h

/-- Every affine chart point is recovered from its classified section line. -/
lemma sectionLinePoint_classify (f : R →+* S) (i : ι) (p : AffineChartPoint R ι f i) :
    sectionLinePoint R ι f i (sectionLineChartEquiv R ι f i p) = p.val ≫ chartMap R ι i := by
  simp only [sectionLinePoint, Equiv.symm_apply_apply]

/-- The represented line point lies over the specified coefficient morphism. -/
@[reassoc]
lemma sectionLinePoint_baseProjection (f : R →+* S) (i : ι)
    (L : NormalizedSectionLine.Chart S ι i) :
    sectionLinePoint R ι f i L ≫ baseProjection R ι = Spec.map (CommRingCat.ofHom f) := by
  rw [sectionLinePoint, Category.assoc, chartMap_baseProjection]
  exact ((sectionLineChartEquiv R ι f i).symm L).property

end FLT.Mazur.ProjectiveSpace
