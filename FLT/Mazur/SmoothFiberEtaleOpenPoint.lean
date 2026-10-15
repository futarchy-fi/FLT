/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothFiberSeparablePoints
public import FLT.Mazur.SmoothEtaleSeparableLift
public import FLT.Mazur.EtaleFiniteGeometricAffine

/-!
# Original affine étale tests meeting geometric smooth opens

A nonempty open in a geometric smooth fiber constructs an affine étale test
of the original base and a geometric lift landing in that open. The chosen
point can change; the geometric base map and the selected open are retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SmoothFiberEtaleOpenPoint
set_option backward.isDefEq.respectTransparency false
variable {R k K : Type} [CommRing R] [Field k] [Field K] [IsSepClosed K] [Algebra k K]
  {V Y U : Scheme}

/-- A geometric smooth open is met by a constructed affine étale original test. -/
theorem exists_point (f : V ⟶ Spec (.of R)) [Smooth f]
    (φ : R →+* k) (hφ : φ.SurjectiveOnStalks)
    (a : Y ⟶ V) (b : Y ⟶ Spec (.of K))
    (H : IsPullback a b f
      (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))))
    (j : U ⟶ Y) [IsOpenImmersion j] (hne : Nonempty U) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of R)) (v : E ⟶ V)
      (z : Spec (.of K) ⟶ E) (u : Spec (.of K) ⟶ U),
      IsAffine E ∧ Etale e ∧ v ≫ f = e ∧
      z ≫ e = Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ)) ∧
      u ≫ j ≫ b = 𝟙 _ ∧ z ≫ v = u ≫ j ≫ a := by
  obtain ⟨y, u, hy, hu, hv⟩ :=
    SmoothFiberSeparablePoints.exists_point f φ a b H j hne
  obtain ⟨E, e, v, z, he, hve, hze, hzv⟩ :=
    SmoothEtaleSeparableLift.exists_lift f φ hφ y hy
  let c := Spec.map (CommRingCat.ofHom (algebraMap (separableClosure k K) K))
  obtain ⟨A, q, w, hA, hq, hw, _⟩ :=
    EtaleFiniteGeometricDiagram.exists_affine_factor (c ≫ z) ⊤ (by trivial)
  refine ⟨A, q ≫ e, q ≫ v, w, u, hA, inferInstance, ?_, ?_, hu, ?_⟩
  · rw [Category.assoc, hve]
  · rw [← Category.assoc, hw, Category.assoc, hze, ← Spec.map_comp]
    congr 1
  · rw [← Category.assoc, hw, Category.assoc, hzv]
    exact hv.symm

end FLT.Mazur.SmoothFiberEtaleOpenPoint
