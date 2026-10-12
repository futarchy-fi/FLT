/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleHilbertAmbientRefinement
public import FLT.Mazur.VariableHilbertCommonAmbientSquare

/-!
# Compatible common ambient neighborhoods of the unrestricted source

The source neighborhoods form an actual scheme open cover. Two choices
containing a finite set have a smaller choice containing that whole set.
In particular, compatibility retains every point of the original full orbit.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) (V : Over (Spec (.of R)))

/-- Refining the original affine ambient refines the actual source support neighborhood. -/
theorem commonAmbientSourceOpen_mono (U T : X.affineOpens) (h : U.val ≤ T.val) :
    commonAmbientSourceOpen f d V U ≤ commonAmbientSourceOpen f d V T := by
  unfold commonAmbientSourceOpen
  rw [← universalAmbientSupport_affine, ← universalAmbientSupport_affine]
  exact (variableFullHilbertParameter f d V).left.preimage_mono
    (universalAmbientSupport_mono f d h)

variable {L : X.Modules} (hL : AmpleLineBundle L)

/-- These actual source neighborhoods cover all unrestricted translated parameters. -/
def commonAmbientSourceCover : (variableHilbertTest f d V).left.OpenCover where
  I₀ := X.affineOpens
  X U := (commonAmbientSourceTest f d V U).left
  f U := (commonAmbientSourceInclusion f d V U).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun U ↦ inferInstance⟩
    obtain ⟨U, hU⟩ := exists_commonAmbientSourceOpen f d V hL {x} (Set.finite_singleton x)
    exact ⟨U, ⟨x, hU (Set.mem_singleton x)⟩, rfl⟩

include hL in
/-- Common source chart choices refine while preserving every point of any finite subset. -/
theorem exists_commonAmbientSource_inter_refinement (U T : X.affineOpens)
    (t : Set (variableHilbertTest f d V).left) (ht : t.Finite)
    (hU : t ⊆ commonAmbientSourceOpen f d V U)
    (hT : t ⊆ commonAmbientSourceOpen f d V T) :
    ∃ B : X.affineOpens, t ⊆ commonAmbientSourceOpen f d V B ∧
      commonAmbientSourceOpen f d V B ≤
        commonAmbientSourceOpen f d V U ⊓ commonAmbientSourceOpen f d V T := by
  let g := (variableFullHilbertParameter f d V).left
  obtain ⟨B, hB, htB⟩ := exists_common_ambient_inter_refinement f d hL U T
    (g '' t) (ht.image g)
    (by rintro _ ⟨x, hx, rfl⟩; exact hU hx)
    (by rintro _ ⟨x, hx, rfl⟩; exact hT hx)
  exact ⟨B, (fun x hx ↦ htB (Set.mem_image_of_mem g hx)), le_inf
    (commonAmbientSourceOpen_mono f d V B U (hB.trans inf_le_left))
    (commonAmbientSourceOpen_mono f d V B T (hB.trans inf_le_right))⟩

include hL in
/-- Compatible refinements retain the WHOLE unrestricted original orbit, not just a basepoint. -/
theorem exists_orbit_commonAmbientSource_refinement [IsAffine V.left] [Etale V.hom]
    (c : (relativeFppfSheaf f).obj.obj (op V)) (x : (variableHilbertTest f d V).left)
    (U T : X.affineOpens)
    (hU : {y | projection (variableChartEquivalenceRelation f hL d V c) y =
      projection (variableChartEquivalenceRelation f hL d V c) x} ⊆
        commonAmbientSourceOpen f d V U)
    (hT : {y | projection (variableChartEquivalenceRelation f hL d V c) y =
      projection (variableChartEquivalenceRelation f hL d V c) x} ⊆
        commonAmbientSourceOpen f d V T) :
    ∃ B : X.affineOpens,
      {y | projection (variableChartEquivalenceRelation f hL d V c) y =
        projection (variableChartEquivalenceRelation f hL d V c) x} ⊆
          commonAmbientSourceOpen f d V B ∧
      commonAmbientSourceOpen f d V B ≤
        commonAmbientSourceOpen f d V U ⊓ commonAmbientSourceOpen f d V T :=
  exists_commonAmbientSource_inter_refinement f d V hL U T _
    (variableChartOrbit_finite f d V c hL x) hU hT

end FLT.Mazur.HilbertChart
