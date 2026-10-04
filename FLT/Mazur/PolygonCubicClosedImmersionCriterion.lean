/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicStalkSurjectivity
public import FLT.Mazur.PolygonCubicProjectiveOver
public import FLT.Mazur.PolygonProper

/-!
# The remaining global closed-immersion criterion

The cubic map is proper and surjective on stalks. Consequently the remaining
global requirement is injectivity of its underlying point map. This module
isolates that requirement; it does not assert that it has been proved.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open PolygonPinching
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The actual projective cubic morphism is proper over its target. -/
lemma cubicProjectiveMorphism_isProper : IsProper (cubicProjectiveMorphism K n hn p q h a) := by
  have := PolygonProper.proper K n hn p q h
  have : IsProper (cubicProjectiveMorphism K n hn p q h a ≫
      ProjectiveSpace.baseProjection K (Fin (n * 3 + 1 + 1))) := by
    rw [cubicProjectiveMorphism_baseProjection]
    infer_instance
  exact IsProper.of_comp _ (ProjectiveSpace.baseProjection K (Fin (n * 3 + 1 + 1)))

/-- After the proved local calculations, global point separation is exactly the remaining gate. -/
theorem cubicProjectiveMorphism_isClosedImmersion_iff_injective :
    IsClosedImmersion (cubicProjectiveMorphism K n hn p q h a) ↔
      Function.Injective (cubicProjectiveMorphism K n hn p q h a) := by
  constructor
  · intro hi
    exact (cubicProjectiveMorphism K n hn p q h a).isClosedEmbedding.injective
  · intro hi
    have := cubicProjectiveMorphism_surjectiveOnStalks K n hn p q h a
    have := cubicProjectiveMorphism_isProper K n hn p q h a
    exact ⟨Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      (cubicProjectiveMorphism K n hn p q h a).continuous hi
      (cubicProjectiveMorphism K n hn p q h a).isClosedMap⟩

end FLT.Mazur.PolygonCubicSections
