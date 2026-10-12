/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianLocalizedTransition
public import FLT.Mazur.GrassmannianPrincipalOverlapScheme

/-!
# Scheme morphisms for localized chart transitions

The rational coordinate formula defines a base-preserving morphism from the
principal overlap to the second affine chart. Precomposition by affine test
maps agrees with composition of its localized polynomial classifying map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R : Type u} [CommRing R] {ι κ : Type u} [Fintype ι] [Fintype κ] {d : ℕ}
  (P : Matrix (Fin d) (Fin d) R) (Q : Matrix ι (Fin d) R)
  (U : Matrix (Fin d) κ R) (T : Matrix ι κ R)

/-- The rational transition as an actual morphism of affine schemes. -/
def localizedChartTransitionScheme :
    principalOverlapScheme P Q ⟶ splitChartScheme R κ d :=
  Spec.map (CommRingCat.ofHom (localizedChartTransitionHom P Q U T).toRingHom)

omit [Fintype κ] in
/-- The transition is over the original coefficient base. -/
theorem localizedChartTransitionScheme_over :
    localizedChartTransitionScheme P Q U T ≫ splitChartStructure R κ d =
      principalOverlapStructure P Q := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (localizedChartTransitionHom P Q U T).comp_algebraMap

variable {S : Type u} [CommRing S] [Algebra R S]

omit [Fintype κ] in
/-- On affine tests the scheme transition is exactly composition of classifying algebra maps. -/
theorem localizedChartTransitionScheme_test (f : principalOverlapRing P Q →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ localizedChartTransitionScheme P Q U T =
      Spec.map (CommRingCat.ofHom (f.comp (localizedChartTransitionHom P Q U T)).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

omit [Fintype κ] in
/-- Every affine test of the transition sends generators to the specialized rational entries. -/
theorem localizedChartTransitionScheme_test_entry (f : principalOverlapRing P Q →ₐ[R] S)
    (i : Fin d) (j : κ) :
    (f.comp (localizedChartTransitionHom P Q U T)) (MvPolynomial.X (i, j)) =
      f (localizedTransitionMatrix P Q U T i j) := by
  rw [AlgHom.comp_apply, localizedChartTransitionHom_entry]

end FLT.Mazur.GrassmannianChart
