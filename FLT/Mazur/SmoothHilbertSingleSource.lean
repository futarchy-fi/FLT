/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothHilbertTestCover
public import FLT.Mazur.RelativePicardCoproductSection

/-!
# A single small scheme presenting the original Picard sheaf

The disjoint union of the fixed smooth charts carries their assembled
original Picard class. Its natural map is locally surjective for the
original fppf topology. This source is a presentation, not a representative.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard OrderedCurvePower
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)

/-- The actual scheme coproduct of the fixed countable chart family. -/
def smoothHilbertSource : Over (Spec (.of R)) :=
  relativeCoproductTest (smoothHilbertTest f)

/-- The unchanged inclusion of one original chart in the assembled source. -/
def smoothHilbertSourceArrow (i : SmoothHilbertTranslationIndex) :
    smoothHilbertTest f i ⟶ smoothHilbertSource f :=
  relativeCoproductArrow (smoothHilbertTest f) i

/-- The original Picard section assembled on the single source scheme. -/
def smoothHilbertSourceSection :
    (relativeFppfSheaf f).obj.obj (op (smoothHilbertSource f)) :=
  relativeCoproductSection f (smoothHilbertTest f)
    (fun i ↦ smoothHilbertPoint f hB i (smoothHilbertTest f i) (𝟙 _))

/-- The assembled section restricts to the unchanged class of every original chart point. -/
theorem smoothHilbertSourceSection_chart (i : SmoothHilbertTranslationIndex)
    {T : Over (Spec (.of R))} (a : T ⟶ smoothHilbertTest f i) :
    (relativeFppfSheaf f).obj.map (a ≫ smoothHilbertSourceArrow f i).op
      (smoothHilbertSourceSection f hB) = smoothHilbertPoint f hB i T a := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  change (relativeFppfSheaf f).obj.map a.op
    ((relativeFppfSheaf f).obj.map (relativeCoproductArrow (smoothHilbertTest f) i).op
      (relativeCoproductSection f (smoothHilbertTest f) _)) = _
  rw [relativeCoproductSection_map, ← smoothHilbertPoint_natural, Category.comp_id]

/-- The single-source map to the original Picard sheaf. -/
def smoothHilbertSourceMap : uliftYoneda.{1}.obj (smoothHilbertSource f) ⟶
    (relativeFppfSheaf f).obj ⋙ forget CommGrpCat :=
  uliftYonedaEquiv.symm (smoothHilbertSourceSection f hB)

/-- Every original section lifts fppf locally to the single actual source scheme. -/
instance smoothHilbertSourceMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of R)))
      (smoothHilbertSourceMap f hB) where
  imageSieve_mem {T} s := by
    apply (Scheme.fppfTopology.over (Spec (.of R))).superset_covering ?_
      (smoothHilbertOverlap_covering f hB T s)
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro U a ⟨i⟩
    refine ⟨ULift.up (smoothHilbertOverlapToChart f hB i T s ≫
      smoothHilbertSourceArrow f i), ?_⟩
    change (relativeFppfSheaf f).obj.map
      (smoothHilbertOverlapToChart f hB i T s ≫ smoothHilbertSourceArrow f i).op
        (smoothHilbertSourceSection f hB) = _
    rw [smoothHilbertSourceSection_chart]
    exact variableHilbertOverlap_class f i.2 hB _ _ T s

end FLT.Mazur.HilbertChart
