/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomLocalNormalizationOrbit
public import FLT.Mazur.CyclicHomLocusNormalizationRelation
public import FLT.Mazur.CyclicHomNormalizedModuli
public import FLT.Mazur.CyclicHomNormalizedRelabelAction

/-!
# Exact local finite relabeling orbits of normalized parameters

At invertible level, equality of original modular classes gives an exact
finite relabeling on an affine neighborhood of every point, even with nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (q r : T ⟶ cyclicHomNormalizedLocus n)

/-- Equal original modular classes lie locally in an exact normalized relabeling orbit. -/
theorem cyclicHomNormalizedModuliMap_local_orbit
    (hn : IsUnit (n : Γ(T, ⊤))) (x : T)
    (h : (cyclicHomNormalizedModuliMap n).app (Opposite.op T) (ULift.up q) =
      (cyclicHomNormalizedModuliMap n).app (Opposite.op T) (ULift.up r)) :
    ∃ (a : MulAut (Labels 4)) (c : MulAut (Multiplicative (ZMod n))) (U : T.Opens),
      IsAffineOpen U ∧ x ∈ U ∧
      U.ι ≫ q ≫ cyclicHomNormalizedRelabel n a c = U.ι ≫ r := by
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
  obtain ⟨a, c, U, hU, hx, he⟩ := cyclicHom_local_normalized_orbit n f g hf hg e hn x
  refine ⟨a, c, U, hU, hx, ?_⟩
  have hL : ((U.ι ≫ qL) ≫ cyclicHomLocusRelabel n a c) ≫ cyclicHomLocusNormalization n =
      (U.ι ≫ rL) ≫ cyclicHomLocusNormalization n := by
    apply (cyclicHomLocusNormalization_eq_iff n _ _).mpr
    simpa only [f, g, Category.assoc, cyclicHomLocusRelabel_inclusion] using he
  simpa only [qL, rL, cyclicHomNormalizedRelabel, Category.assoc,
    cyclicHomNormalizedLocusInclusion_normalization, Category.comp_id] using hL

end FLT.Mazur.UniversalWeierstrass
