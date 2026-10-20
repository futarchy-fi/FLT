/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomNormalizedLocalOrbit
public import FLT.Mazur.OddWeierstrassCyclicHomNormalizedLocalOrbit
public import FLT.Mazur.CyclicCharacteristicProductParameterGroupoid

/-!
# Exact local same-chart orbits at invertible level

This retains an affine neighborhood of every test point and equality of
actual endpoint morphisms, including on nonreduced test schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (b : Bool) (q r : T ⟶ normalizedLocus n b)

/-- Equal modular classes in either chart have exact local common relabelings. -/
theorem normalizedModuliMap_local_orbit
    (hn : IsUnit (n : Γ(T, ⊤))) (x : T)
    (h : (normalizedModuliMap n b).app (Opposite.op (T)) (ULift.up q) =
      (normalizedModuliMap n b).app (Opposite.op (T)) (ULift.up r)) :
    ∃ (e : RelabelGroup n) (U : T.Opens), IsAffineOpen U ∧ x ∈ U ∧
      U.ι ≫ q ≫ (normalizedRelabelAction n b e).hom = U.ι ≫ r := by
  cases b
  · obtain ⟨a, c, U, hU, hx, he⟩ :=
      UniversalWeierstrass.cyclicHomNormalizedModuliMap_local_orbit n q r hn x h
    exact ⟨⟨a, 1, c⟩, U, hU, hx, he⟩
  · obtain ⟨a, c, U, hU, hx, he⟩ :=
      OddWeierstrassParameter.cyclicHomNormalizedModuliMap_local_orbit n q r hn x h
    exact ⟨⟨1, a, c⟩, U, hU, hx, he⟩

/-- A full compatible comparison gives an exact local finite relabeling of its endpoints. -/
theorem compatible_local_sameChart_orbit
    (hn : IsUnit (n : Γ(T, ⊤))) (x : T)
    (a : CompatibleIso ((normalizedSubgroup n b).baseChange q)
      ((normalizedSubgroup n b).baseChange r)) :
    ∃ (e : RelabelGroup n) (U : T.Opens), IsAffineOpen U ∧ x ∈ U ∧
      U.ι ≫ q ≫ (normalizedRelabelAction n b e).hom = U.ι ≫ r := by
  apply normalizedModuliMap_local_orbit n b q r hn x
  rw [normalizedModuliMap_eq_pullback, normalizedModuliMap_eq_pullback]
  exact Quotient.sound ⟨a⟩

/-- Full same-chart parameters retain exact locally relabeled endpoints. -/
theorem productArrow_local_sameChart_orbit
    (hn : IsUnit (n : Γ(T, ⊤))) (x : T) (a : ProductArrow n q r) :
    ∃ (e : RelabelGroup n) (U : T.Opens), IsAffineOpen U ∧ x ∈ U ∧
      U.ι ≫ q ≫ (normalizedRelabelAction n b e).hom = U.ι ≫ r :=
  compatible_local_sameChart_orbit n b q r hn x
    (productCompatibleTestComparison n b b q r a)

end FLT.Mazur.CyclicCharacteristicAtlas
