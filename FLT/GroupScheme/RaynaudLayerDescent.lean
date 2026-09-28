/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudTorsorDescent

/-!
# Descent through arbitrary finite flat layers

The Hopf torsor and faithful flatness reduce middle-map surjectivity to the
comparison maps on subgroup closures and contracted quotients. Neither layer
has a prescribed order. The order-three quotient specialization leaves only
the subgroup comparison for induction.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- Over a common contracted quotient, surjectivity on the flat kernel closure
descends to surjectivity of the middle map, with no bound on either layer. -/
theorem GenericGaloisHom.middle_surjective_of_common_quotient_of_kernel
    {S X X' Y : FF ℤ_[3] ℚ_[3]} (i : GenericGaloisHom S X)
    (q : GenericGaloisHom X Y) (hi : Function.Injective i) (hq : Function.Surjective q)
    (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x)
    (g : ModelHom X X') (hj : Function.Injective ((genericHom g).comp i))
    (k' : ModelHom X' (q.flatQuotient hq))
    (hc : g.comp k' = q.toFlatQuotient hq)
    (hker : Function.Surjective (i.closureMap hi g hj)) : Function.Surjective g := by
  let := q.quotientCoordinates_flat
  let := q.quotientCoordinates_faithfullyFlat
  let k : q.quotientCoordinates →ₐc[ℤ_[3]] X'.CoordinateRing := k'
  let := k.toAlgHom.toAlgebra
  have : IsScalarTower ℤ_[3] q.quotientCoordinates X'.CoordinateRing :=
    IsScalarTower.of_algebraMap_eq' k.toAlgHom.comp_algebraMap.symm
  have hs : Function.Surjective ((i.closureInclusion hi).comp g) := by
    rw [← i.closureMap_comp_inclusion hi g hj]
    exact hker.comp
      Ideal.Quotient.mk_surjective
  apply HopfAlgebra.surjective_of_kernel_of_faithfullyFlat k (by ext; rfl)
    q.quotientInclusion (by ext; rfl) g hc
  change Function.Surjective ((Ideal.Quotient.mkₐ ℤ_[3] q.quotientKernelIdeal).comp g.toAlgHom)
  rw [i.quotientKernelIdeal_eq_closureIdeal_of_relative_flat q hq hexact]
  exact hs

/-- In a compatible diagram, an invertible quotient comparison and a surjective
subgroup comparison force the middle map to be surjective on coordinates. -/
theorem GenericGaloisHom.middle_surjective_of_layer_maps
    {S X X' Y Y' : FF ℤ_[3] ℚ_[3]} (i : GenericGaloisHom S X)
    (q : GenericGaloisHom X Y) (q' : GenericGaloisHom X' Y')
    (hi : Function.Injective i) (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x)
    (g : ModelHom X X') (hj : Function.Injective ((genericHom g).comp i))
    (h : GenericGaloisHom Y Y') (hc : q'.comp (genericHom g) = h.comp q)
    (hker : Function.Surjective (i.closureMap hi g hj))
    (hquot : Function.Bijective (q.flatQuotientMap q' hq hq' g h hc)) :
    Function.Surjective g := by
  let e := BialgEquiv.ofBijective (q.flatQuotientMap q' hq hq' g h hc)
    hquot
  let k' : ModelHom X' (q.flatQuotient hq) := (q'.toFlatQuotient hq').comp e.symm.toBialgHom
  have hk : g.comp k' = q.toFlatQuotient hq := by
    ext d
    have he := DFunLike.congr_fun
      (q.toFlatQuotient_comp_flatQuotientMap q' hq hq' g h hc) (e.symm d)
    change q.toFlatQuotient hq (e (e.symm d)) = g (k' d) at he
    rw [e.apply_symm_apply] at he
    exact he.symm
  exact i.middle_surjective_of_common_quotient_of_kernel q hi hq hexact g hj k' hk hker

/-- For an order-three quotient, the only remaining input to middle-map
surjectivity is surjectivity of the comparison on subgroup closures. -/
theorem GenericGaloisHom.middle_surjective_of_order_three_quotient
    {S X X' Y Y' : FF ℤ_[3] ℚ_[3]} (i : GenericGaloisHom S X)
    (q : GenericGaloisHom X Y) (q' : GenericGaloisHom X' Y')
    (hi : Function.Injective i) (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x)
    (g : ModelHom X X') (hj : Function.Injective ((genericHom g).comp i))
    (h : GenericGaloisHom Y Y') (hc : q'.comp (genericHom g) = h.comp q)
    (hh : Function.Surjective h) (hY : Nat.card Y.Points = 3) (hY' : Nat.card Y'.Points = 3)
    (hker : Function.Surjective (i.closureMap hi g hj)) : Function.Surjective g :=
  i.middle_surjective_of_layer_maps q q' hi hq hq' hexact g hj h hc hker
    (q.flatQuotientMap_bijective_of_order_three q' hq hq' g h hc hh hY hY')

end ThreeAdicPlan
