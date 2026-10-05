/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteAffineIntersectionDiagram
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Gluing finite intersection-shaped scheme diagrams

Cartesian union squares make an intersection-shaped diagram locally directed.
If its arrows are open immersions, Mathlib's locally directed gluing constructs
actual scheme glue data, including transition maps on overlaps and the
triple-pullback cocycle. This applies also to the descended model diagrams.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {ι : Type v} (F : (NonemptyChartSet ι)ᵒᵖ ⥤ Scheme.{u})

/-- Cartesian union squares imply the pointwise condition required for gluing. -/
theorem intersectionDiagram_isLocallyDirected
    (hp : ∀ (r s t : NonemptyChartSet ι) (hrs : r ≤ s) (hrt : r ≤ t),
      IsPullback
        (F.map (homOfLE (le_unionChartSet_left s t)).op)
        (F.map (homOfLE (le_unionChartSet_right s t)).op)
        (F.map (homOfLE hrs).op) (F.map (homOfLE hrt).op)) :
    (F ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro i j k fi fj xi xj h
  have hsq := hp k.unop i.unop j.unop (leOfHom fi.unop) (leOfHom fj.unop)
  obtain ⟨x, hx, hy⟩ := Scheme.exists_preimage_of_isPullback hsq xi xj h
  exact ⟨Opposite.op (unionChartSet i.unop j.unop),
    (homOfLE (le_unionChartSet_left i.unop j.unop)).op,
    (homOfLE (le_unionChartSet_right i.unop j.unop)).op, x, hx, hy⟩

variable [Finite ι] [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]
  (hp : ∀ (r s t : NonemptyChartSet ι) (hrs : r ≤ s) (hrt : r ≤ t),
    IsPullback
      (F.map (homOfLE (le_unionChartSet_left s t)).op)
      (F.map (homOfLE (le_unionChartSet_right s t)).op)
      (F.map (homOfLE hrs).op) (F.map (homOfLE hrt).op))

/-- Glue the actual diagram, with transitions and cocycle constructed on its pullbacks. -/
def intersectionDiagramGlueData : Scheme.GlueData.{u} := by
  letI := intersectionDiagram_isLocallyDirected F hp
  exact Scheme.IsLocallyDirected.glueData F

/-- The constructed gluing admits the original diagram as an open cover. -/
def intersectionDiagramGluedCover :
    (intersectionDiagramGlueData F hp).glued.OpenCover :=
  (intersectionDiagramGlueData F hp).openCover

/-- The glue-data transition maps satisfy the cocycle on the actual triple pullback. -/
theorem intersectionDiagramGlueData_cocycle
    (i j k : (intersectionDiagramGlueData F hp).J) :
    (intersectionDiagramGlueData F hp).t' i j k ≫
      (intersectionDiagramGlueData F hp).t' j k i ≫
      (intersectionDiagramGlueData F hp).t' k i j = 𝟙 _ :=
  (intersectionDiagramGlueData F hp).cocycle i j k

/-- Naturally isomorphic intersection diagrams have isomorphic constructed gluings. -/
def intersectionDiagramGluingIsoOfNatIso
    (G : (NonemptyChartSet ι)ᵒᵖ ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (G.map f)]
    (hq : ∀ (r s t : NonemptyChartSet ι) (hrs : r ≤ s) (hrt : r ≤ t),
      IsPullback
        (G.map (homOfLE (le_unionChartSet_left s t)).op)
        (G.map (homOfLE (le_unionChartSet_right s t)).op)
        (G.map (homOfLE hrs).op) (G.map (homOfLE hrt).op))
    (e : F ≅ G) :
    (intersectionDiagramGlueData F hp).glued ≅ (intersectionDiagramGlueData G hq).glued := by
  letI := intersectionDiagram_isLocallyDirected F hp
  letI := intersectionDiagram_isLocallyDirected G hq
  exact (Scheme.IsLocallyDirected.isColimit F).coconePointUniqueUpToIso
    (Limits.colimit.isColimit F) ≪≫
    Limits.HasColimit.isoOfNatIso e ≪≫
    (Limits.colimit.isColimit G).coconePointUniqueUpToIso (Scheme.IsLocallyDirected.isColimit G)

end FLT.Mazur.Approximation
