/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonAtlas

/-!
# Comparison with any specified polygon pinching cocone

The constructed atlas is canonically isomorphic to every pushout of the same
specified endpoint diagram. Local finite presentation follows from the actual
node and Laurent charts and transports through this comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.PolygonPinching
variable (K : Type u) [Field K]

/-- The cyclic atlas is locally of finite presentation over K. -/
theorem cyclic_lfp (n : ℕ) (h : 2 ≤ n) :
    LocallyOfFinitePresentation (PolygonCyclicAtlas.toBase K n h) := by
  let U : (PolygonCyclicAtlas.scheme K n h).OpenCover :=
    Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (Fin n)
      (fun _ ↦ PolygonNodeBranches.node K) (PolygonCyclicAtlas.chart K n h)
      (fun x ↦ by
        obtain ⟨i, y, hy⟩ := PolygonCyclicAtlas.charts_cover K n h x
        exact ⟨i, y, hy⟩) (fun _ ↦ inferInstance)
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation) U
  intro i
  change LocallyOfFinitePresentation
    (PolygonCyclicAtlas.chart K n h i ≫ PolygonCyclicAtlas.toBase K n h)
  rw [PolygonCyclicAtlas.chart_toBase]
  infer_instance

/-- The irreducible one-gon atlas is locally of finite presentation over K. -/
theorem oneGon_lfp : LocallyOfFinitePresentation (OneGonGluing.toBase K) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation)
    (BinaryOpenDescent.cover (OneGonGluing.node K) (OneGonGluing.torus K)
      (OneGonGluing.charts_cover K))
  intro i
  cases i
  · change LocallyOfFinitePresentation (OneGonGluing.node K ≫ OneGonGluing.toBase K)
    rw [OneGonGluing.node_toBase]
    infer_instance
  · change LocallyOfFinitePresentation (OneGonGluing.torus K ≫ OneGonGluing.toBase K)
    rw [OneGonGluing.torus_toBase]
    change LocallyOfFinitePresentation (MultiplicativeGroupScheme.gm K).hom
    infer_instance

/-- Every positive polygon atlas is locally of finite presentation. -/
instance atlas_lfp (n : ℕ) [NeZero n] :
    LocallyOfFinitePresentation (PolygonAtlas.polygon K n).hom := by
  rcases n with _ | (_ | n)
  · exact False.elim (NeZero.ne 0 rfl)
  · exact oneGon_lfp K
  · exact cyclic_lfp K (n + 2) (by omega)

variable (n : ℕ) [NeZero n] (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- Canonical comparison of the exact specified pinching cocones. -/
def polygonIso : PolygonAtlas.polygon K n ≅ C :=
  (PolygonAtlas.isPushout K n hn).isoIsPushout _ _ h

@[reassoc (attr := simp)]
theorem normalization_polygonIso :
    PolygonAtlas.normalization K n ≫ (polygonIso K n hn p q h).hom = p :=
  (PolygonAtlas.isPushout K n hn).inl_isoIsPushout_hom _ _ h

@[reassoc (attr := simp)]
theorem nodes_polygonIso :
    PolygonAtlas.nodes K n ≫ (polygonIso K n hn p q h).hom = q :=
  (PolygonAtlas.isPushout K n hn).inr_isoIsPushout_hom _ _ h

@[reassoc (attr := simp)]
theorem normalization_polygonIso_inv :
    p ≫ (polygonIso K n hn p q h).inv = PolygonAtlas.normalization K n :=
  (PolygonAtlas.isPushout K n hn).inl_isoIsPushout_inv _ _ h

@[reassoc (attr := simp)]
theorem nodes_polygonIso_inv :
    q ≫ (polygonIso K n hn p q h).inv = PolygonAtlas.nodes K n :=
  (PolygonAtlas.isPushout K n hn).inr_isoIsPushout_inv _ _ h

include h in
/-- Local finite presentation is a consequence of the pinching cocone. -/
theorem polygon_lfp : LocallyOfFinitePresentation C.hom := by
  have : IsIso (polygonIso K n hn p q h).inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (polygonIso K n hn p q h).inv))
  rw [← (polygonIso K n hn p q h).inv.w]
  infer_instance

end FLT.Mazur.PolygonPinching
