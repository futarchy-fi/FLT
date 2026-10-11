/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothHilbertSingleSource

/-!
# A single smooth cover carrying lifts into the Picard presentation

The actual disjoint union of the represented intersections is a smooth
surjective fppf cover of the original test. Its map into the assembled
source retains exactly the supplied original Picard-sheaf section.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard OrderedCurvePower
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- The actual disjoint union of all original chart-test intersections. -/
def smoothHilbertIntersectionSource : Over (Spec (.of R)) :=
  relativeCoproductTest (fun i ↦ smoothHilbertOverlap f hB i T s)

/-- The jointly surjective intersection family assembled into one test morphism. -/
def smoothHilbertIntersectionToTest : smoothHilbertIntersectionSource f hB T s ⟶ T :=
  Over.homMk (Sigma.desc (fun i ↦ (smoothHilbertOverlapToTest f hB i T s).left)) (by
    apply Sigma.hom_ext
    intro i
    change Sigma.ι _ i ≫ Sigma.desc _ ≫ T.hom = Sigma.ι _ i ≫ Sigma.desc _
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Over.w])

/-- The single test-cover morphism is smooth. -/
instance smoothHilbertIntersectionToTest_smooth :
    Smooth (smoothHilbertIntersectionToTest f hB T s).left := by
  change Smooth (Sigma.desc (fun i ↦ (smoothHilbertOverlapToTest f hB i T s).left))
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Smooth) (fun _ ↦ inferInstance)

/-- The single test-cover morphism is surjective. -/
instance smoothHilbertIntersectionToTest_surjective :
    Surjective (smoothHilbertIntersectionToTest f hB T s).left :=
  SchemeFppfFamily.projection_surjective (smoothHilbertTestCover f hB T s)

/-- Each original intersection retains its exact test projection in the assembled cover. -/
theorem smoothHilbertIntersectionToTest_chart (i : SmoothHilbertTranslationIndex) :
    relativeCoproductArrow (fun j ↦ smoothHilbertOverlap f hB j T s) i ≫
      smoothHilbertIntersectionToTest f hB T s = smoothHilbertOverlapToTest f hB i T s :=
  Over.OverMorphism.ext (Sigma.ι_comp_desc _ _)

/-- The assembled cover maps to the fixed single source using the original chart maps. -/
def smoothHilbertIntersectionToSource :
    smoothHilbertIntersectionSource f hB T s ⟶ smoothHilbertSource f :=
  Over.homMk (Sigma.desc (fun i ↦
    (smoothHilbertOverlapToChart f hB i T s ≫ smoothHilbertSourceArrow f i).left)) (by
      apply Sigma.hom_ext
      intro i
      change Sigma.ι _ i ≫ Sigma.desc _ ≫ (smoothHilbertSource f).hom =
        Sigma.ι _ i ≫ Sigma.desc _
      rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Over.w])

/-- The source map retains every original intersection's chart map. -/
theorem smoothHilbertIntersectionToSource_chart (i : SmoothHilbertTranslationIndex) :
    relativeCoproductArrow (fun j ↦ smoothHilbertOverlap f hB j T s) i ≫
      smoothHilbertIntersectionToSource f hB T s =
        smoothHilbertOverlapToChart f hB i T s ≫ smoothHilbertSourceArrow f i :=
  Over.OverMorphism.ext (Sigma.ι_comp_desc _ _)

/-- The smooth cover lifts exactly the supplied original Picard-sheaf section. -/
theorem smoothHilbertIntersectionSource_class :
    (relativeFppfSheaf f).obj.map (smoothHilbertIntersectionToSource f hB T s).op
      (smoothHilbertSourceSection f hB) =
        (relativeFppfSheaf f).obj.map (smoothHilbertIntersectionToTest f hB T s).op s := by
  apply relativeCoproductSection_ext f (fun i ↦ smoothHilbertOverlap f hB i T s)
  intro i
  dsimp only [smoothHilbertIntersectionSource] at *
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    smoothHilbertIntersectionToSource_chart, smoothHilbertIntersectionToTest_chart,
    smoothHilbertSourceSection_chart]
  exact variableHilbertOverlap_class f i.2 hB _ _ T s

end FLT.Mazur.HilbertChart
