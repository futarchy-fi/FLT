/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfTorsorDescent
public import FLT.GroupScheme.RaynaudFlatKernelExactness
public import FLT.GroupScheme.RaynaudFiltrationLayers
public import FLT.GroupScheme.RaynaudQuotientFlatness

/-!
# Middle-map descent for order-three layers

Relative flatness and the Hopf torsor identify a comparison with its map on
kernel coordinates after faithful flat base change. This covers every contracted
quotient, including unramified quotients and nonsplit generic extensions.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- Every contracted three-adic Hopf quotient is faithfully flat. -/
theorem GenericGaloisHom.quotientCoordinates_faithfullyFlat
    {X Y : FF ℤ_[3] ℚ_[3]} (q : GenericGaloisHom X Y) :
    Module.FaithfullyFlat q.quotientCoordinates X.CoordinateRing := by
  let := q.quotientCoordinates_flat
  let : Module.Finite q.quotientCoordinates X.CoordinateRing :=
    Module.Finite.of_restrictScalars_finite ℤ_[3] q.quotientCoordinates X.CoordinateRing
  exact Module.FaithfullyFlat.of_comap_surjective
    (Algebra.IsIntegral.comap_surjective q.quotientCoordinates X.CoordinateRing)

/-- Over a common contracted quotient, order-three subgroup rigidity forces
surjectivity of the middle comparison, without a splitting or ramification condition. -/
theorem GenericGaloisHom.middle_surjective_of_common_quotient
    {S X X' Y : FF ℤ_[3] ℚ_[3]} (i : GenericGaloisHom S X)
    (q : GenericGaloisHom X Y) (hi : Function.Injective i) (hq : Function.Surjective q)
    (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x) (hS : Nat.card S.Points = 3)
    (g : ModelHom X X') (hj : Function.Injective ((genericHom g).comp i))
    (k' : ModelHom X' (q.flatQuotient hq))
    (hc : g.comp k' = q.toFlatQuotient hq) : Function.Surjective g := by
  let := q.quotientCoordinates_flat
  let := q.quotientCoordinates_faithfullyFlat
  let k : q.quotientCoordinates →ₐc[ℤ_[3]] X'.CoordinateRing := k'
  let := k.toAlgHom.toAlgebra
  have : IsScalarTower ℤ_[3] q.quotientCoordinates X'.CoordinateRing :=
    IsScalarTower.of_algebraMap_eq' k.toAlgHom.comp_algebraMap.symm
  have hs : Function.Surjective ((i.closureInclusion hi).comp g) := by
    rw [← i.closureMap_comp_inclusion hi g hj]
    exact (i.closureMap_bijective_of_order_three hi g hj hS).2.comp
      Ideal.Quotient.mk_surjective
  apply HopfAlgebra.surjective_of_kernel_of_faithfullyFlat k (by ext; rfl)
    q.quotientInclusion (by ext; rfl) g hc
  change Function.Surjective ((Ideal.Quotient.mkₐ ℤ_[3] q.quotientKernelIdeal).comp g.toAlgHom)
  rw [i.quotientKernelIdeal_eq_closureIdeal_of_relative_flat q hq hexact]
  exact hs

/-- A comparison of order-three subgroup and quotient layers is surjective on
middle coordinate rings. This applies uniformly to all order-three quotients. -/
theorem GenericGaloisHom.middle_surjective_of_order_three_layers
    {S X X' Y Y' : FF ℤ_[3] ℚ_[3]} (i : GenericGaloisHom S X)
    (q : GenericGaloisHom X Y) (q' : GenericGaloisHom X' Y')
    (hi : Function.Injective i) (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x) (hS : Nat.card S.Points = 3)
    (g : ModelHom X X') (hj : Function.Injective ((genericHom g).comp i))
    (h : GenericGaloisHom Y Y') (hc : q'.comp (genericHom g) = h.comp q)
    (hh : Function.Surjective h) (hY : Nat.card Y.Points = 3) (hY' : Nat.card Y'.Points = 3) :
    Function.Surjective g := by
  let e := BialgEquiv.ofBijective (q.flatQuotientMap q' hq hq' g h hc)
    (q.flatQuotientMap_bijective_of_order_three q' hq hq' g h hc hh hY hY')
  let k' : ModelHom X' (q.flatQuotient hq) := (q'.toFlatQuotient hq').comp e.symm.toBialgHom
  have hk : g.comp k' = q.toFlatQuotient hq := by
    ext d
    have he := DFunLike.congr_fun
      (q.toFlatQuotient_comp_flatQuotientMap q' hq hq' g h hc) (e.symm d)
    change q.toFlatQuotient hq (e (e.symm d)) = g (k' d) at he
    rw [e.apply_symm_apply] at he
    exact he.symm
  exact i.middle_surjective_of_common_quotient q hi hq hexact hS g hj k' hk

end ThreeAdicPlan
