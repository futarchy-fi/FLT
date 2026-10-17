/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicHomRetainedSubgroup
public import FLT.Mazur.CartierGeneratorOrbitRecovery

/-!
# The pointed cubic cover retains the prescribed original generator

The universal source label one is the actual pulled Cartier generator in
the retained subgroup. This identifies the choice made by orbit reconstruction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open UniversalWeierstrass FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₂ : IsUnit (2 : Γ(S, ⊤))) {n : ℕ} [NeZero n]
  (H : (pointedCubicFamily W).FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
local notation "φ" => H.generatorCurveMarking hP
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₂)
local notation "f" => Over.Hom.left (pointedCubicHomAuxiliaryParameter W h₂ φ)
local notation "J" => pointedCubicHomRetainedSubgroup W h₂ φ H
local notation "hJ" => pointedCubicHomRetained_ideal W h₂ φ H hP rfl

/-- The chosen source orbit generator is precisely the pulled original Cartier generator. -/
theorem pointedCubicHomRetained_orbitGenerator :
    (J).orbitGenerator (cyclicHomSourceMarking n f) hJ = H.pullGenerator k P :=
  (J).orbitGenerator_eq_of_generatorMarking
    (pointedCubicHomRetained_generator W h₂ φ H hP) _ hJ
    (pointedCubicHomRetained_marking W h₂ φ H hP rfl)

/-- Every chosen universal orbit label retains the corresponding original generator power. -/
theorem pointedCubicHomRetained_orbit_power (m : ℕ) :
    (J).orbitMarking (cyclicHomSourceMarking n f) hJ (.ofAdd (m : ZMod n)) =
      H.pullGenerator k P ^ m := by
  rw [← orbitGenerator_pow, pointedCubicHomRetained_orbitGenerator]

/-- The full original comparison carries its pulled generator to the specified source generator. -/
theorem pointedCubicHomRetainedIso_orbitGenerator :
    H.pullGenerator k P ≫ (pointedCubicHomRetainedIso W h₂ φ H).subgroup.hom =
      (J).orbitGenerator (cyclicHomSourceMarking n f) hJ := by
  rw [pointedCubicHomRetained_orbitGenerator]
  exact Category.comp_id _

end FLT.Mazur.GeneralizedEllipticCurve
