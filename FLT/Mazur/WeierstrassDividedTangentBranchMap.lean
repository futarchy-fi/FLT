/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchResidue

/-!
# Strict-branch formulas commute with coefficient specialization

Denominator equations identify the constructed inverses after every ring map.
Thus residue calculations apply to the actual output coordinates, rather than
to an independently chosen residue formula.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s b3 a2 b4' b6' u₁ u₂ v₁ v₂ : R)
  (hc : IsUnit (v₁ + W.a₁ * u₁ + b3))
  (hd : IsUnit (v₁ + v₂ + W.a₁ * u₂ + b3))
  (hc' : IsUnit (f v₁ + (W.map f).a₁ * f u₁ + f b3))
  (hd' : IsUnit (f v₁ + f v₂ + (W.map f).a₁ * f u₂ + f b3))
local notation "k" => tangentBranchSlope W b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd
local notation "k'" => tangentBranchSlope (W.map f) (f b3) (f a2) (f b4') (f b6')
  (f u₁) (f u₂) (f v₁) (f v₂) hc' hd'

/-- The branch ordinate commutes with arbitrary ring homomorphisms. -/
theorem tangentBranchOrdinate_map :
    f (tangentBranchOrdinate W b3 a2 b4' b6' u₁ v₁ hc) =
      tangentBranchOrdinate (W.map f) (f b3) (f a2) (f b4') (f b6') (f u₁) (f v₁) hc' := by
  apply hc'.mul_left_inj.mp
  rw [tangentBranchOrdinate_denominator]
  simpa only [map_add, map_mul, map_pow, map_a₁] using
    congrArg f (tangentBranchOrdinate_denominator W b3 a2 b4' b6' u₁ v₁ hc)

/-- The divided slope is the same construction after specialization. -/
theorem tangentBranchSlope_map : f k = k' := by
  apply hd'.mul_left_inj.mp
  rw [tangentBranchSlope_denominator]
  have h := congrArg f (tangentBranchSlope_denominator W b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd)
  simpa only [map_add, map_mul, map_pow, map_sub, map_a₁,
    tangentBranchOrdinate_map f W b3 a2 b4' b6' u₁ v₁ hc hc'] using h

/-- The actual divided abscissa specializes to the residue construction. -/
theorem tangentBranchX_map :
    f (tangentBranchX W s a2 u₁ u₂ k) =
      tangentBranchX (W.map f) (f s) (f a2) (f u₁) (f u₂) k' := by
  simp only [tangentBranchX, map_add, map_mul, map_pow, map_sub, map_a₁,
    tangentBranchSlope_map f W b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd hc' hd']

/-- The actual divided ordinate specializes to the residue construction. -/
theorem tangentBranchY_map :
    f (tangentBranchY W s b3 a2 u₁ u₂ v₁ k) =
      tangentBranchY (W.map f) (f s) (f b3) (f a2) (f u₁) (f u₂) (f v₁) k' := by
  simp only [tangentBranchY, tangentBranchX, map_add, map_mul, map_pow,
    map_sub, map_neg, map_a₁,
    tangentBranchSlope_map f W b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd hc' hd']

end FLT.Mazur.WeierstrassDilatation
