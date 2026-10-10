/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSectionSpecialFiber
public import FLT.Mazur.EllipticPrimeSubgroupComponents

/-!
# The original cyclic subgroup in the geometric special-fiber component

The component injection retains every member of the original subgroup.
For a prime-order generator outside E₀, the zero element is its only cyclic
subgroup member whose actual specialized section lies in the smooth zero
component. No group structure is placed on the singular cubic itself.
-/

@[expose] public noncomputable section

open AlgebraicGeometry IsLocalRing

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {K : Type u} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- An injective component subgroup meets the genuine smooth zero component only at zero. -/
theorem subgroupClosedFiber_zero_component_iff
    (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point)
    (hi : Function.Injective (ellipticSubgroupComponentHom A W H)) (P : H) :
    Set.range (integralPointClosedFiber A W P.val) ⊆
        (integralSmoothOpen (W.map (residue A))).ι ''
          connectedComponent (integralSmoothZero (W.map (residue A))
            (closedPoint (ResidueField A))) ↔ P = 0 := by
  rw [integralPointClosedFiber_zero_component_iff]
  constructor
  · intro h
    apply hi
    exact ((ellipticComponentHom_eq_zero A W P.val).mpr h).trans
      (map_zero (ellipticSubgroupComponentHom A W H)).symm
  · rintro rfl
    exact smoothReduction_zero A W

/-- The component map is injective on the exact cyclic subgroup of a prime point outside E₀. -/
theorem primePoint_component_injective_of_not_smooth
    (p : ℕ) [Fact p.Prime] (P : (W.map (algebraMap A K)).toProjective.Point)
    (ho : addOrderOf P = p) (hs : ¬ SmoothReduction A W P) :
    Function.Injective (ellipticSubgroupComponentHom A W (AddSubgroup.zmultiples P)) := by
  have hc : Nat.card (AddSubgroup.zmultiples P) = p := (Nat.card_zmultiples P).trans ho
  apply (primeSubgroup_smooth_or_component_injective A W _ p hc).resolve_left
  exact fun h => hs (h (AddSubgroup.mem_zmultiples P))

/-- Every nonzero member of this original prime cyclic subgroup avoids the smooth zero component. -/
theorem primePointClosedFiber_zero_component_iff
    (p : ℕ) [Fact p.Prime] (P : (W.map (algebraMap A K)).toProjective.Point)
    (ho : addOrderOf P = p) (hs : ¬ SmoothReduction A W P)
    (T : AddSubgroup.zmultiples P) :
    Set.range (integralPointClosedFiber A W T.val) ⊆
        (integralSmoothOpen (W.map (residue A))).ι ''
          connectedComponent (integralSmoothZero (W.map (residue A))
            (closedPoint (ResidueField A))) ↔ T = 0 :=
  subgroupClosedFiber_zero_component_iff A W _
    (primePoint_component_injective_of_not_smooth A W p P ho hs) T

end FLT.Mazur.WeierstrassIntegralChart
