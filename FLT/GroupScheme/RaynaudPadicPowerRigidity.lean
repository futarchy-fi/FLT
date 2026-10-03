/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudLocalPowerRigidity

/-!
# Integral rigidity over the original p-adic integers

The rational-place comparison and its fraction-field lift transport actual
models. Their point groups retain the annihilating exponent; faithful flat
reflection returns surjectivity to the original p-adic coordinate rings.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ThreeAdicPlan
open NumberField IsLocalRing

variable (p : ℕ) [Fact p.Prime]

/-- Odd-prime p-adic models killed by a power of p admit no proper generic isomorphisms. -/
theorem ModelHom.surjective_of_padic_power (hp : 2 < p) {n : ℕ}
    {X Y : FF ℤ_[p] ℚ_[p]} (hX : ∀ x : X.Points, p ^ n • x = 0)
    (g : ModelHom X Y) (hg : Function.Bijective (genericHom g)) : Function.Surjective g := by
  let v := LocalCyclotomic.rationalPlace p
  let O := v.adicCompletionIntegers ℚ
  let Kv := v.adicCompletion ℚ
  let eR : ℤ_[p] ≃+* O :=
    (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨p, Fact.out⟩).toAlgEquiv.toRingEquiv
  let : Algebra ℤ_[p] O := eR.toRingHom.toAlgebra
  let fR : ℤ_[p] →+* Kv := (algebraMap O Kv).comp eR.toRingHom
  let : Algebra ℤ_[p] Kv := fR.toAlgebra
  let : IsScalarTower ℤ_[p] O Kv := .of_algebraMap_eq' rfl
  have hfR : Function.Injective fR := (IsFractionRing.injective O Kv).comp eR.injective
  let : Algebra ℚ_[p] Kv := (IsFractionRing.lift hfR : ℚ_[p] →+* Kv).toAlgebra
  let : IsScalarTower ℤ_[p] ℚ_[p] Kv := .of_algebraMap_eq fun r ↦
    (IsFractionRing.lift_algebraMap hfR r).symm
  let : IsAdicComplete (maximalIdeal O) O := rationalCompletionIntegers_adicComplete p
  let : CharP (ResidueField O) p := (LocalCyclotomic.residueEquiv p).toRingHom.charP
    (LocalCyclotomic.residueEquiv p).injective p
  let : Module.FaithfullyFlat ℤ_[p] O := RingHom.FaithfullyFlat.of_bijective eR.bijective
  have hπ : Irreducible (p : O) := by
    simpa only [map_natCast] using (MulEquiv.irreducible_iff (f := eR)).mpr PadicInt.irreducible_p
  have he : RaynaudParameters.order (p : O) < p - 1 := by
    rw [RaynaudParameters.order, IsDiscreteValuationRing.addVal_uniformizer hπ]
    simp only [ENat.toNat_one]
    omega
  let e := (X.restrictedScalarExtension O Kv).inversePoints
  have he' : Function.Surjective e := (X.restrictedScalarExtension O Kv).pointsEquiv.symm.surjective
  have hXS : ∀ x : (X.scalarExtension O Kv).Points, p ^ n • x = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := he' y
    exact (map_nsmul e (p ^ n) x).symm.trans ((congrArg e (hX x)).trans (map_zero e))
  have h := (g.scalarExtension O Kv).surjective_of_local_power v p he hXS
    (g.generic_bijective_scalarExtension O Kv hg)
  exact (Module.FaithfullyFlat.lTensor_surjective_iff_surjective ℤ_[p] O
    g.toAlgHom.toLinearMap).mp h

end ThreeAdicPlan
