/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstantCyclicGenerator
public import FLT.Mazur.PolygonCyclicDivisor
/-!
# Cyclicity as an equality of actual Cartier divisors

The powers of the constant-group generator, transported through the divisor
isomorphism, recover every marked section. Their scheme-theoretic sum is
exactly the all-one divisor, as an equality of quasi-coherent ideal sheaves.
-/

open CategoryTheory Limits AlgebraicGeometry MonObj MonoidalCategory CartesianMonoidalCategory
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCyclicDivisorOrbit
open PolygonPinching PolygonCyclicDivisor PolygonBoundaryDivisor
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  {C : Over (Spec (.of K))} (p : components K n ⟶ C)
  (hn : 0 < n) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
local notation "S" => Spec (CommRingCat.of K)
local notation "I" => ideal K n p (fun _ ↦ 1)

/-- The generator of the constant cyclic group of sections. -/
abbrev generator : 𝟙_ (Over S) ⟶ ConstantCyclicGroup.model S n :=
  ConstantCyclicGroup.component S n 1

/-- A generator power transported into the actual polygon curve. -/
def orbitSection (i : Fin n) : S ⟶ C.left :=
  ((generator K n ^ i.val) ≫ (overIso K n p hn q h).hom).left ≫ (I).subschemeι

/-- The generator power is precisely the specified marked section. -/
theorem orbitSection_eq (i : Fin n) :
    orbitSection K n p hn q h i = PolygonMarkedSections.sectionMap K n p 1 i := by
  rw [orbitSection, generator, ← ConstantCyclicGenerator.component_pow]
  exact component_schemeIso_ι K n p hn q h i

/-- The all-one divisor is the scheme-theoretic sum of generator powers. -/
theorem cyclic_divisor : (I) = ∏ i, (orbitSection K n p hn q h i).ker := by
  simp only [orbitSection_eq]
  rfl
end FLT.Mazur.PolygonCyclicDivisorOrbit
