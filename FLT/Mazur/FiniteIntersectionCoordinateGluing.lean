/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionDiagramGluing
public import FLT.Mazur.FiniteIntersectionCoordinateSquares
public import FLT.Mazur.FiniteIntersectionGluingRecovery

/-!
# Gluing the actual affine coordinate diagram

The spectrum diagram of the section algebras is naturally isomorphic to the
open intersection diagram. Its constructed gluing therefore recovers the
covered scheme. This connects affine coordinates, actual pullback gluing,
and recovery; scalar extension of descended gluing is a further step.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {ι : Type v}
  (U : ι → X.Opens) (p : X ⟶ Spec (.of A)) [X.IsSeparated]
  (hU : ∀ i, IsAffineOpen (U i))

/-- Simultaneous, arrow-compatible recovery of the entire affine coordinate diagram. -/
def finiteIntersectionCoordinateDiagramIso :
    finiteIntersectionSchemeDiagram U ≅
      affineIntersectionSchemeDiagram (finiteIntersectionSectionDiagram U p) :=
  NatIso.ofComponents (fun a ↦ finiteIntersectionSectionSpecIso U p hU a.unop)
    (fun f ↦ (finiteIntersectionSectionSpecIso_naturality U p hU f.unop).symm)

variable [Finite ι]

/-- The actual section-algebra diagram has constructed scheme glue data. -/
def finiteIntersectionCoordinateGlueData : Scheme.GlueData.{u} := by
  letI := fun a b (f : a ⟶ b) ↦
    finiteIntersectionSectionDiagram_map_isOpenImmersion U p hU f
  exact affineIntersectionGlueData (finiteIntersectionSectionDiagram U p)
    (finiteIntersectionSectionDiagram_isPullback U p hU)

/-- Gluing the actual affine coordinates recovers the original covered scheme. -/
def finiteIntersectionCoordinateGluingIso (hcover : iSup U = ⊤) :
    (finiteIntersectionCoordinateGlueData U p hU).glued ≅ X := by
  let C := finiteIntersectionSectionDiagram U p
  let F := affineIntersectionSchemeDiagram C
  letI : ∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f) :=
    fun {_ _} f ↦ finiteIntersectionSectionDiagram_map_isOpenImmersion U p hU f.unop
  letI := intersectionDiagram_isLocallyDirected F
    (finiteIntersectionSectionDiagram_isPullback U p hU)
  exact (Scheme.IsLocallyDirected.isColimit F).coconePointUniqueUpToIso (colimit.isColimit F) ≪≫
    HasColimit.isoOfNatIso (finiteIntersectionCoordinateDiagramIso U p hU).symm ≪≫
    (colimit.isColimit (finiteIntersectionSchemeDiagram U)).coconePointUniqueUpToIso
      (finiteIntersectionSchemeCoconeIsColimit U hcover)

end FLT.Mazur.Approximation
