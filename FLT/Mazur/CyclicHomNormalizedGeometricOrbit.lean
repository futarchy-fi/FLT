/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomGeometricNormalizationOrbit
public import FLT.Mazur.CyclicHomLocusNormalizationRelation
public import FLT.Mazur.CyclicHomNormalizedModuli
public import FLT.Mazur.CyclicHomNormalizedRelabelAction

/-!
# Geometric fibers of the normalized modular map are finite relabeling orbits

Equality of original modular classes yields a compatible source comparison.
Marked rigidity then identifies the actual normalized scheme-valued parameters.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {K : Type} [Field K] [IsAlgClosed K]
  (q r : Spec (.of K) ⟶ cyclicHomNormalizedLocus n)

/-- Equal geometric modular classes lie in one actual normalized relabeling orbit. -/
theorem cyclicHomNormalizedModuliMap_geometric_orbit
    (h : (cyclicHomNormalizedModuliMap n).app (Opposite.op (Spec (.of K))) (ULift.up q) =
      (cyclicHomNormalizedModuliMap n).app (Opposite.op (Spec (.of K))) (ULift.up r)) :
    ∃ (a : MulAut (Labels 4)) (c : MulAut (Multiplicative (ZMod n))),
      q ≫ cyclicHomNormalizedRelabel n a c = r := by
  let qL := q ≫ cyclicHomNormalizedLocusInclusion n
  let rL := r ≫ cyclicHomNormalizedLocusInclusion n
  let f := qL ≫ cyclicHomUniversalMultiplicationLocusInclusion n
  let g := rL ≫ cyclicHomUniversalMultiplicationLocusInclusion n
  have hf : cyclicHomMultiplicationEquation n f = 0 :=
    (cyclicHomUniversalLocus_factorization_iff_equation n f).mp ⟨qL, rfl⟩
  have hg : cyclicHomMultiplicationEquation n g = 0 :=
    (cyclicHomUniversalLocus_factorization_iff_equation n g).mp ⟨rL, rfl⟩
  change cyclicHomSourceModuliClass n f hf = cyclicHomSourceModuliClass n g hg at h
  obtain ⟨e⟩ := Quotient.exact h
  obtain ⟨a, c, he⟩ := cyclicHom_geometric_normalized_orbit n f g hf hg e
  refine ⟨a, c, ?_⟩
  have hL : (qL ≫ cyclicHomLocusRelabel n a c) ≫ cyclicHomLocusNormalization n =
      rL ≫ cyclicHomLocusNormalization n := by
    apply (cyclicHomLocusNormalization_eq_iff n _ _).mpr
    simpa only [f, g, Category.assoc, cyclicHomLocusRelabel_inclusion] using he
  simpa only [qL, rL, cyclicHomNormalizedRelabel, Category.assoc,
    cyclicHomNormalizedLocusInclusion_normalization, Category.comp_id] using hL

end FLT.Mazur.UniversalWeierstrass
