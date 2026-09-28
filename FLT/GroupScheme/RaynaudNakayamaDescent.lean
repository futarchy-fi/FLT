/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudFlatKernelExactness
public import FLT.GroupScheme.RaynaudFiltrationLayers
public import Mathlib.RingTheory.Nakayama

/-!
# Descent of surjectivity from the kernel over a Jacobson augmentation

A comparison of finite algebras over a fixed quotient is surjective if it is
surjective on the actual kernel and the quotient augmentation ideal lies in
the Jacobson radical. Nakayama supplies the middle-map step in this case.
-/

@[expose] public noncomputable section

namespace AlgHom

variable {D A B : Type*} [CommRing D] [CommRing A] [CommRing B]
    [Algebra D A] [Algebra D B]

/-- Surjectivity on a fibre defined by a Jacobson ideal descends to a finite
algebra map, by Nakayama's lemma. -/
theorem surjective_of_quotient_map_of_le_jacobson [Module.Finite D B]
    (f : A →ₐ[D] B) (I : Ideal D) (hI : I ≤ (⊥ : Ideal D).jacobson)
    (hf : Function.Surjective
      ((Ideal.Quotient.mkₐ D (I.map (algebraMap D B))).comp f)) :
    Function.Surjective f := by
  apply f.toLinearMap.surjective_of_surjective_comp_mkQ I hI
  intro z
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ z
  obtain ⟨a, ha⟩ := hf (Ideal.Quotient.mk (I.map (algebraMap D B)) b)
  refine ⟨a, ?_⟩
  change Submodule.Quotient.mk (f a) = Submodule.Quotient.mk b
  apply (Submodule.Quotient.eq _).mpr
  rw [Ideal.smul_top_eq_map]
  exact (Ideal.Quotient.eq.mp ha)

end AlgHom

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    {D X X' : FF R K}

/-- A comparison over a common quotient is surjective when its restriction to
the scheme kernel is surjective and the augmentation is a Jacobson ideal. -/
theorem ModelHom.surjective_of_quotient_kernel_of_le_jacobson
    (g : ModelHom X X') (k : ModelHom X D) (k' : ModelHom X' D)
    (hc : g.comp k' = k)
    (hJ : RingHom.ker (Bialgebra.counitAlgHom R D.CoordinateRing).toRingHom ≤
      (⊥ : Ideal D.CoordinateRing).jacobson)
    (hg : Function.Surjective
      ((Ideal.Quotient.mkₐ R
        ((RingHom.ker (Bialgebra.counitAlgHom R D.CoordinateRing).toRingHom).map
          k.toAlgHom.toRingHom)).comp g.toAlgHom)) :
    Function.Surjective g := by
  let := k.toAlgHom.toAlgebra
  let := k'.toAlgHom.toAlgebra
  have : IsScalarTower R D.CoordinateRing X.CoordinateRing :=
    IsScalarTower.of_algebraMap_eq' k.toAlgHom.comp_algebraMap.symm
  have : IsScalarTower R D.CoordinateRing X'.CoordinateRing :=
    IsScalarTower.of_algebraMap_eq' k'.toAlgHom.comp_algebraMap.symm
  let : Module.Finite D.CoordinateRing X.CoordinateRing :=
    Module.Finite.of_restrictScalars_finite R D.CoordinateRing X.CoordinateRing
  let f : X'.CoordinateRing →ₐ[D.CoordinateRing] X.CoordinateRing :=
    { __ := g.toAlgHom.toRingHom
      commutes' d := DFunLike.congr_fun hc d }
  exact f.surjective_of_quotient_map_of_le_jacobson _ hJ hg

/-- Over a quotient with Jacobson augmentation, relative flatness and order-three
subgroup rigidity force a comparison of middle models to be surjective. -/
theorem GenericGaloisHom.middle_surjective_of_relative_flat_of_le_jacobson
    {S X X' Y : FF ℤ_[3] ℚ_[3]} (i : GenericGaloisHom S X)
    (q : GenericGaloisHom X Y) (hi : Function.Injective i) (hq : Function.Surjective q)
    (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x) (hS : Nat.card S.Points = 3)
    (g : ModelHom X X') (hj : Function.Injective ((genericHom g).comp i))
    (k' : ModelHom X' (q.flatQuotient hq))
    (hc : g.comp k' = q.toFlatQuotient hq)
    [Module.Flat q.quotientCoordinates X.CoordinateRing]
    (hJ : RingHom.ker (Bialgebra.counitAlgHom ℤ_[3] q.quotientCoordinates).toRingHom ≤
      (⊥ : Ideal q.quotientCoordinates).jacobson) : Function.Surjective g := by
  have hs : Function.Surjective ((i.closureInclusion hi).comp g) := by
    rw [← i.closureMap_comp_inclusion hi g hj]
    exact (i.closureMap_bijective_of_order_three hi g hj hS).2.comp
      Ideal.Quotient.mk_surjective
  apply g.surjective_of_quotient_kernel_of_le_jacobson (q.toFlatQuotient hq) k' hc hJ
  change Function.Surjective ((Ideal.Quotient.mkₐ ℤ_[3] q.quotientKernelIdeal).comp g.toAlgHom)
  rw [i.quotientKernelIdeal_eq_closureIdeal_of_relative_flat q hq hexact]
  exact hs

/-- The quotient comparison isomorphism supplies a common integral quotient for
an order-three comparison diagram; Nakayama then proves the middle surjective. -/
theorem GenericGaloisHom.middle_surjective_of_order_three_layers_of_le_jacobson
    {S X X' Y Y' : FF ℤ_[3] ℚ_[3]} (i : GenericGaloisHom S X)
    (q : GenericGaloisHom X Y) (q' : GenericGaloisHom X' Y')
    (hi : Function.Injective i) (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x) (hS : Nat.card S.Points = 3)
    (g : ModelHom X X') (hj : Function.Injective ((genericHom g).comp i))
    (h : GenericGaloisHom Y Y') (hc : q'.comp (genericHom g) = h.comp q)
    (hh : Function.Surjective h) (hY : Nat.card Y.Points = 3) (hY' : Nat.card Y'.Points = 3)
    [Module.Flat q.quotientCoordinates X.CoordinateRing]
    (hJ : RingHom.ker (Bialgebra.counitAlgHom ℤ_[3] q.quotientCoordinates).toRingHom ≤
      (⊥ : Ideal q.quotientCoordinates).jacobson) : Function.Surjective g := by
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
  exact i.middle_surjective_of_relative_flat_of_le_jacobson q hi hq hexact hS g hj k' hk hJ

end ThreeAdicPlan
