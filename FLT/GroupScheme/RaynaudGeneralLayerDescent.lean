/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralQuotientFaithfullyFlat
public import FLT.GroupScheme.HopfTorsorDescent
public import FLT.GroupScheme.RaynaudFiltrationLayers

/-!
# Middle-map descent over arbitrary principal ideal domains

Faithful flatness of the actual contracted quotient identifies the integral
kernel with its generic closure. Kernel and quotient comparisons then force
surjectivity of the middle comparison, with no restriction on layer orders.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsDedekindDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]

/-- Over a common contracted quotient, surjectivity on the flat kernel closure
descends to surjectivity of the middle map, with no bound on either layer. -/
theorem GenericGaloisHom.middle_surjective_of_common_quotient_of_kernel_pid
    {S X X' Y : FF R K} (i : GenericGaloisHom S X)
    (q : GenericGaloisHom X Y) (hi : Function.Injective i) (hq : Function.Surjective q)
    (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x)
    (g : ModelHom X X') (hj : Function.Injective ((genericHom g).comp i))
    (k' : ModelHom X' (q.flatQuotient hq))
    (hc : g.comp k' = q.toFlatQuotient hq)
    (hker : Function.Surjective (i.closureMap hi g hj)) : Function.Surjective g := by
  let := q.quotientCoordinatesFaithfullyFlat
  let k : q.quotientCoordinates →ₐc[R] X'.CoordinateRing := k'
  let := k.toAlgHom.toAlgebra
  have : IsScalarTower R q.quotientCoordinates X'.CoordinateRing :=
    IsScalarTower.of_algebraMap_eq' k.toAlgHom.comp_algebraMap.symm
  have hs : Function.Surjective ((i.closureInclusion hi).comp g) := by
    rw [← i.closureMap_comp_inclusion hi g hj]
    exact hker.comp
      Ideal.Quotient.mk_surjective
  apply HopfAlgebra.surjective_of_kernel_of_faithfullyFlat k (by ext; rfl)
    q.quotientInclusion (by ext; rfl) g hc
  change Function.Surjective ((Ideal.Quotient.mkₐ R q.quotientKernelIdeal).comp g.toAlgHom)
  rw [i.quotientKernelIdeal_eq_closureIdeal_of_relative_flat q hq hexact]
  exact hs

/-- In a compatible diagram, an invertible quotient comparison and a surjective
subgroup comparison force the middle map to be surjective on coordinates. -/
theorem GenericGaloisHom.middle_surjective_of_layer_maps_pid
    {S X X' Y Y' : FF R K} (i : GenericGaloisHom S X)
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
  exact i.middle_surjective_of_common_quotient_of_kernel_pid q hi hq hexact g hj k' hk hker

end ThreeAdicPlan
