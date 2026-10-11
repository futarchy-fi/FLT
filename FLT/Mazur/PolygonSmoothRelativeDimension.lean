/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MultiplicativeGroupDimension
public import FLT.Mazur.PolygonSmoothLocus

/-!
# Relative dimension of the actual polygon smooth locus

The specified Laurent components cover the entire smooth locus, including
for a one-gon. Each component is a relative curve over the coefficient field.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonPinching

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  [LocallyOfFinitePresentation C.hom]

/-- The existing Laurent components give an actual open cover of the polygon smooth locus. -/
def smoothComponentOpenCover : (smoothPolygon K (C := C)).left.OpenCover where
  I₀ := ZMod n
  X _ := (MultiplicativeGroupScheme.gm K).left
  f i := (smoothComponent K n hn p q h i).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    have hx : x ∈ (⨆ i, (smoothComponent K n hn p q h i).left.opensRange) := by
      rw [smoothComponent_cover K n hn p q h]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx

include h in
/-- The whole actual smooth locus of a specified polygon has relative dimension one. -/
theorem smoothPolygon_relativeDimension :
    SmoothOfRelativeDimension 1 (smoothPolygon K (C := C)).hom := by
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1)
    (smoothComponentOpenCover K n hn p q h)
  intro i
  change SmoothOfRelativeDimension 1
    ((smoothComponent K n hn p q h i).left ≫ (smoothPolygon K (C := C)).hom)
  rw [(smoothComponent K n hn p q h i).w]
  exact MultiplicativeGroupDimension.dimension K

/-- In particular, the original cyclic polygon smooth locus is a relative curve. -/
theorem cyclic_smoothLocus_relativeDimension (K : Type u) [Field K]
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    let _ := cyclic_lfp K n hn
    SmoothOfRelativeDimension 1
      ((PolygonCyclicAtlas.toBase K n hn).smoothLocus.ι ≫ PolygonCyclicAtlas.toBase K n hn) := by
  let _ := cyclic_lfp K n hn
  let _ : LocallyOfFinitePresentation (PolygonCyclicAtlas.polygon K n hn).hom :=
    cyclic_lfp K n hn
  exact smoothPolygon_relativeDimension K n (by omega)
    (PolygonCyclicAtlas.normalization K n hn) (PolygonCyclicAtlas.nodes K n hn)
    (PolygonCyclicPushout.isPushout K n hn (by omega))

end FLT.Mazur.PolygonPinching
