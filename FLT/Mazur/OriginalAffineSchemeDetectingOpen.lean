/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalAffineFiberDetectingOpen
public import FLT.Mazur.OriginalAffineFiberCoordinates

/-!
# Uniform detecting opens for original affine schemes

Geometric integrality supplies the tensor domain condition. The detecting
open lives on the actual algebraic fiber and retains the whole projection
of every selected rational point to the original scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OriginalAffineSchemeDetectingOpen
open AffineScalarFiberComparison OriginalAffineFiberCoordinates
open TranscendentalCoefficientOrbitAvoidance
set_option backward.isDefEq.respectTransparency false
variable {k L K : Type} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra k K] [IsScalarTower k L K]
  [Algebra.IsAlgebraic k L] {X Y Z : Scheme} [IsAffine X]

/-- The actual algebraic fiber contains a uniformly detecting nonempty open. -/
theorem exists_detecting_open (f : X ⟶ Spec (.of k)) [GeometricallyIntegral f]
    (a : Y ⟶ Spec (.of K)) (b : Y ⟶ X)
    (H : IsPullback a b (Spec.map (CommRingCat.ofHom (algebraMap k K))) f)
    (c : Z ⟶ Spec (.of L)) (d : Z ⟶ X)
    (G : IsPullback c d (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)
    {J : Type*} [Finite J] (U : J → Y.Opens)
    (hU : ∀ j, (U j : Set Y).Nonempty) :
    ∃ W : Z.Opens, (W : Set Z).Nonempty ∧
      ∀ p : Spec (.of L) ⟶ Z, p ≫ c = 𝟙 _ → Set.range p ⊆ W →
        ∃ z : (L ≃ₐ[k] L) → (Spec (.of K) ⟶ Y),
          (∀ σ, z σ ≫ a = 𝟙 _) ∧
          (∀ σ, z σ ≫ b = Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
            Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ p ≫ d) ∧
          ∀ σ j, Set.range (z σ) ⊆ U j := by
  let _ := (scalarMap f).toAlgebra
  let _ := tensor_isDomain f L
  obtain ⟨W, hW, hall⟩ := exists_fiber_detecting_open a (b ≫ X.isoSpec.hom)
    (coordinate_square f a b H) c (d ≫ X.isoSpec.hom) (coordinate_square f c d G) U hU
  refine ⟨W, hW, fun p hp hm ↦ ?_⟩
  obtain ⟨z, hz, hd, hm⟩ := hall p hp hm
  refine ⟨z, hz, fun σ ↦ ?_, hm⟩
  rw [← cancel_mono X.isoSpec.hom]
  simpa only [Category.assoc] using hd σ

end FLT.Mazur.OriginalAffineSchemeDetectingOpen
