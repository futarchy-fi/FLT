/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalAffineFiberCoordinates
public import FLT.Mazur.OriginalAffineFiberOrbit

/-!
# Whole original affine scheme points in transcendental opens

For an original affine geometrically integral scheme of finite type, every
finite family of nonempty larger-field opens contains a whole algebraic point
orbit. Finite type and the integral tensor premise are derived geometrically.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OriginalAffineSchemeOrbit
open AffineScalarFiberComparison OriginalAffineFiberCoordinates
open TranscendentalCoefficientOrbitAvoidance
set_option backward.isDefEq.respectTransparency false
variable {k L K : Type} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra k K] [IsScalarTower k L K]
  [Algebra.IsAlgebraic k L] [IsAlgClosed L]
  {X Y : Scheme} [IsAffine X] (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [GeometricallyIntegral f]
  (a : Y ⟶ Spec (.of K)) (b : Y ⟶ X)
  (H : IsPullback a b (Spec.map (CommRingCat.ofHom (algebraMap k K))) f)

include H in
/-- The original scheme point and every conjugate retain their whole coefficient morphisms. -/
theorem exists_point_orbit {J : Type*} [Finite J]
    (U : J → Y.Opens) (hU : ∀ j, (U j : Set Y).Nonempty) :
    ∃ (q : Spec (.of L) ⟶ X) (z : (L ≃ₐ[k] L) → (Spec (.of K) ⟶ Y)),
      q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧
      (∀ σ, z σ ≫ a = 𝟙 _) ∧
      (∀ σ, z σ ≫ b = Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ q) ∧
      ∀ σ j, Set.range (z σ) ⊆ U j := by
  let _ := (scalarMap f).toAlgebra
  let _ := sections_finiteType f
  let _ := tensor_isDomain f L
  obtain ⟨q, z, hz, hq, hU⟩ := exists_original_morphism_orbit_in_opens (L := L)
    a (b ≫ X.isoSpec.hom) (coordinate_square f a b H) U hU
  refine ⟨originalPointMorphism q ≫ X.isoSpec.inv, z, ?_, hz, ?_, hU⟩
  · rw [Category.assoc, ← coordinate_map f, originalPointMorphism, ← Spec.map_comp]
    congr 1
    ext r
    exact q.commutes r
  · intro σ
    rw [← cancel_mono X.isoSpec.hom]
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hq σ

end FLT.Mazur.OriginalAffineSchemeOrbit
