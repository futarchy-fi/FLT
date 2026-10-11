/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothGeometricSeparablePoints
public import FLT.Mazur.LocallyFiniteTypeSeparablePointFactor

/-!
# Finite separable witnesses inside every smooth geometric open

The representative selected in the specified geometric open factors through
an actual finite separable field. This factorization retains that same
point, its original projection, and its geometric field structure.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SmoothGeometricFiniteSeparablePoints
set_option backward.isDefEq.respectTransparency false
variable {k K : Type} [Field k] [Field K] [IsSepClosed K] [Algebra k K]
  {X Y : Scheme}

/-- Every nonempty smooth geometric open has an exact finite separable original representative. -/
theorem exists_point (f : X ⟶ Spec (.of k)) [Smooth f]
    (a : Y ⟶ X) (b : Y ⟶ Spec (.of K))
    (H : IsPullback a b f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (W : Set Y) (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ (L : IntermediateField k (separableClosure k K))
      (y : Spec (.of L) ⟶ X) (z : Spec (.of K) ⟶ Y),
      Module.Finite k L ∧ Algebra.IsSeparable k L ∧ z default ∈ W ∧
      z ≫ b = 𝟙 _ ∧ y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧
      z ≫ a = Spec.map (CommRingCat.ofHom
        ((algebraMap (separableClosure k K) K).comp
          (algebraMap L (separableClosure k K)))) ≫ y := by
  obtain ⟨y₀, z, hzW, hzK, hy₀, hz⟩ :=
    SmoothGeometricSeparablePoints.exists_point f a b H W hW hne
  obtain ⟨L, y, hfin, hsep, hy, he⟩ :=
    LocallyFiniteTypeSeparablePointFactor.exists_factor f y₀ hy₀
  refine ⟨L, y, z, hfin, hsep, hzW, hzK, hy, ?_⟩
  rw [hz, ← he, ← Category.assoc, ← Spec.map_comp]
  rfl

end FLT.Mazur.SmoothGeometricFiniteSeparablePoints
