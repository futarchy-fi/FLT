/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBaseSectionFunctor
public import FLT.Mazur.FiniteAffineIntersectionDiagram

/-!
# Affine coordinates on the finite intersection diagram

The actual intersections, with their structural maps, define a diagram over
`Spec A`. Taking sections supplies compatible base algebras and restriction
maps. Affineness gives natural spectrum identifications, and geometric local
finite presentation gives finite presentations without an extra algebraic hypothesis.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {ι : Type v}
  (U : ι → X.Opens) (p : X ⟶ Spec (.of A))

/-- The intersection diagram equipped with its actual maps to the affine base. -/
def finiteIntersectionOverDiagram : (NonemptyChartSet ι)ᵒᵖ ⥤ Over (Spec (.of A)) :=
  finiteIntersectionOpenDiagram U ⋙ X.restrictFunctor ⋙ Over.map p

/-- The covariant diagram of section algebras and restriction homomorphisms. -/
def finiteIntersectionSectionDiagram : NonemptyChartSet ι ⥤ CommAlgCat A :=
  (finiteIntersectionOverDiagram U p).rightOp ⋙ affineBaseSectionFunctor A

/-- Forgetting the base structure recovers precisely the original intersection diagram. -/
theorem finiteIntersectionOverDiagram_forget :
    finiteIntersectionOverDiagram U p ⋙ Over.forget _ =
      finiteIntersectionSchemeDiagram U := rfl

/-- Finite intersection coordinates are affine under the geometric separation hypothesis. -/
theorem finiteIntersectionOverDiagram_isAffine [X.IsSeparated]
    (hU : ∀ i, IsAffineOpen (U i)) (s : NonemptyChartSet ι) :
    IsAffine ((finiteIntersectionOverDiagram U p).obj (Opposite.op s)).left :=
  finiteIntersectionSchemeDiagram_isAffine U hU (Opposite.op s)

/-- Recover each actual intersection from its section algebra. -/
def finiteIntersectionSectionSpecIso [X.IsSeparated]
    (hU : ∀ i, IsAffineOpen (U i)) (s : NonemptyChartSet ι) :
    (finiteIntersectionSchemeDiagram U).obj (Opposite.op s) ≅
      Spec ((forget₂ (CommAlgCat A) CommRingCat).obj
        ((finiteIntersectionSectionDiagram U p).obj s)) := by
  letI := finiteIntersectionOverDiagram_isAffine U p hU s
  exact affineBaseSectionsSpecIso A ((finiteIntersectionOverDiagram U p).obj (Opposite.op s))

/-- Coordinate restriction maps recover the actual geometric inclusion maps. -/
@[reassoc]
theorem finiteIntersectionSectionSpecIso_naturality [X.IsSeparated]
    (hU : ∀ i, IsAffineOpen (U i)) {s t : NonemptyChartSet ι} (f : s ⟶ t) :
    (finiteIntersectionSectionSpecIso U p hU t).hom ≫
      Spec.map (CommRingCat.ofHom (((finiteIntersectionSectionDiagram U p).map f).hom.toRingHom)) =
        (finiteIntersectionSchemeDiagram U).map f.op ≫
          (finiteIntersectionSectionSpecIso U p hU s).hom := by
  let := finiteIntersectionOverDiagram_isAffine U p hU s
  let := finiteIntersectionOverDiagram_isAffine U p hU t
  exact affineBaseSectionsSpecIso_naturality A ((finiteIntersectionOverDiagram U p).map f.op)

/-- Local finite presentation restricts to each intersection's structure map. -/
instance finiteIntersectionOverDiagram_locallyOfFinitePresentation
    [LocallyOfFinitePresentation p] (s : NonemptyChartSet ι) :
    LocallyOfFinitePresentation
      ((finiteIntersectionOverDiagram U p).obj (Opposite.op s)).hom := by
  change LocallyOfFinitePresentation ((finiteIntersectionOpen U s).ι ≫ p)
  infer_instance

/-- Finite presentations of intersection section algebras follow from geometry. -/
theorem finiteIntersectionSectionDiagram_finitePresentation [X.IsSeparated]
    [LocallyOfFinitePresentation p] (hU : ∀ i, IsAffineOpen (U i)) (s : NonemptyChartSet ι) :
    Algebra.FinitePresentation A ((finiteIntersectionSectionDiagram U p).obj s) := by
  let := finiteIntersectionOverDiagram_isAffine U p hU s
  exact affineBaseSections_finitePresentation A
    ((finiteIntersectionOverDiagram U p).obj (Opposite.op s))

/-- Choose actual finite presentations of all intersection section algebras together. -/
theorem finiteIntersectionSectionDiagram_presentations [X.IsSeparated]
    [LocallyOfFinitePresentation p] (hU : ∀ i, IsAffineOpen (U i)) :
    ∃ n m : NonemptyChartSet ι → ℕ,
      Nonempty (∀ s, Algebra.Presentation A ((finiteIntersectionSectionDiagram U p).obj s)
        (Fin (n s)) (Fin (m s))) := by
  let := finiteIntersectionSectionDiagram_finitePresentation U p hU
  exact ⟨fun s ↦ Algebra.Presentation.ofFinitePresentationVars A
      ((finiteIntersectionSectionDiagram U p).obj s),
    fun s ↦ Algebra.Presentation.ofFinitePresentationRels A
      ((finiteIntersectionSectionDiagram U p).obj s),
    ⟨fun s ↦ Algebra.Presentation.ofFinitePresentation A
      ((finiteIntersectionSectionDiagram U p).obj s)⟩⟩

end FLT.Mazur.Approximation
