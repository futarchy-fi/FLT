/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.GlobalModelAwayTwo
/-!
# Global finite-flat models over the integers

An étale model over the ring with three inverted is patched with a
finite-flat model over the three-adic integers. The rational bialgebra comparison
identifies the resulting geometric points with the prescribed Galois module.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance 100000] CommRing.toCommSemiring CommSemiring.toSemiring
  Algebra.toSMul Algebra.toModule
open scoped TensorProduct
namespace ThreeAdicPlan
namespace PadicPatching

/-- Three does not divide the global denominator. -/
local instance notThreeDvdOne : Fact (¬ ((3 : ℕ) : ℤ) ∣ (1 : ℤ)) := ⟨by norm_num⟩
/-- The excluded integers are prime. -/
local instance : Fact (∀ p ∈ ({3} : Finset ℕ), p.Prime) :=
  ⟨by simp [Nat.prime_three]⟩

/-- Inverting one gives the integer coefficient ring. -/
local instance : Algebra (Base 1) ℤ := baseOneEquivInt.toRingEquiv.toRingHom.toAlgebra

/-- The rational embedding of the coefficient ring with one inverted. -/
local instance : Algebra (Base 1) ℚ := Algebra.compHom ℚ (algebraMap (Base 1) ℤ)

/-- The rational embedding factors through the integer coefficient ring. -/
local instance : IsScalarTower (Base 1) ℤ ℚ := by
  exact integerLocalizationScalarTower 1 (Base 1) ℤ ℚ

/-- The two presentations of the ring with three inverted agree. -/
def awayThreeEquiv : ZInvPrimes {3} ≃ₐ[ℤ] Away 1 3 := by
  convert (awayEquivSingle 3 1).symm using 1
  norm_num [ZInvPrimes]

/-- The away ring is an algebra over its single-localization presentation. -/
local instance : Algebra (ZInvPrimes {3}) (Away 1 3) :=
  awayThreeEquiv.toRingEquiv.toRingHom.toAlgebra

/-- The canonical rational embedding of the away coefficient ring. -/
local instance : Algebra (Away 1 3) ℚ :=
  (IsLocalization.Away.lift (3 : Base 1)
    (show IsUnit (algebraMap (Base 1) ℚ 3) by
      rw [map_ofNat]
      exact isUnit_iff_ne_zero.mpr (show (3 : ℚ) ≠ 0 by decide))).toAlgebra

/-- The single localization acts on the local field through the rationals. -/
local instance : Algebra (ZInvPrimes {3}) ℚ_[3] :=
  Algebra.compHom ℚ_[3] (algebraMap (ZInvPrimes {3}) ℚ)
/-- The coefficient embeddings form a compatible scalar tower. -/
local instance : IsScalarTower (ZInvPrimes {3}) ℚ ℚ_[3] :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The coefficient embeddings form a compatible scalar tower. -/
local instance : IsScalarTower (Base 1) (Away 1 3) ℚ :=
  by exact integerLocalizationScalarTower 1 (Base 1) (Away 1 3) ℚ
/-- The coefficient embeddings form a compatible scalar tower. -/
local instance : IsScalarTower (Base 1) ℚ ℚ_[3] :=
  by exact integerLocalizationScalarTower 1 _ _ _
/-- The coefficient embeddings form a compatible scalar tower. -/
local instance : IsScalarTower (Away 1 3) ℚ ℚ_[3] :=
  integerLocalizationScalarTower ((1 : ℤ) * (3 : ℕ)) _ _ _
/-- The coefficient embeddings form a compatible scalar tower. -/
local instance : IsScalarTower (ZInvPrimes {3}) (Away 1 3) ℚ :=
  integerLocalizationScalarTower (∏ p ∈ ({3} : Finset ℕ), (p : ℤ)) _ _ _
/-- The coefficient embeddings form a compatible scalar tower. -/
local instance : IsScalarTower (ZInvPrimes {3}) (Away 1 3) ℚ_[3] :=
  integerLocalizationScalarTower (∏ p ∈ ({3} : Finset ℕ), (p : ℤ)) _ _ _

/-- The model away from three, presented over the iterated localization
used by arithmetic patching. -/
def awayThreeModel (W : FiniteContinuousGaloisModule)
    (hur : UnramifiedOutside {3} W) : FiniteEtaleModel (Away 1 3) W := by
  let I := W.integralEtaleModel {3} hur
  let A := Away 1 3 ⊗[ZInvPrimes {3}] I.CoordinateRing
  let : HopfAlgebra.IsFiniteFlat (Away 1 3) A := ⟨⟩
  let E : ℚ ⊗[Away 1 3] A ≃ₐc[ℚ] W.GenericCoordinateAlgebra :=
    (bialgebraCancelBaseChange (ZInvPrimes {3}) (Away 1 3) ℚ I.CoordinateRing).trans
      (W.integralEtaleModelGenericEquiv {3} hur)
  exact { toHasFiniteFlatModel := HasFiniteFlatModel.ofGenericBialgEquiv W A E
          etale := by change Algebra.Etale (Away 1 3) A; infer_instance }

/-- The away and local models have the same local generic bialgebra. -/
def awayThreeLocalComparison (W : FiniteContinuousGaloisModule)
    (hur : UnramifiedOutside {3} W) (h3 : HasFiniteFlatModel ℤ_[3] W.localAtThree) :
    ℚ_[3] ⊗[ℤ_[3]] h3.CoordinateRing ≃ₐc[ℚ_[3]]
      ℚ_[3] ⊗[Away 1 3] (awayThreeModel W hur).CoordinateRing :=
  (W.localModelGenericBialgEquiv h3).symm.trans
    ((bialgebraBaseChangeEquiv ℚ ℚ_[3] _ _
      (awayThreeModel W hur).toHasFiniteFlatModel.genericBialgEquiv).trans
        (bialgebraCancelBaseChange (Away 1 3) ℚ ℚ_[3]
          (awayThreeModel W hur).CoordinateRing))

/-- A local finite-flat model at three glues to the étale model away from three,
producing a finite-flat model over `ℤ`. -/
def globalModelOverInt (W : FiniteContinuousGaloisModule)
    (h3 : HasFiniteFlatModel ℤ_[3] W.localAtThree)
    (hur : UnramifiedOutside {3} W) : ModelOverInt W := by
  let M := awayThreeModel W hur
  let A := M.CoordinateRing
  let B := h3.CoordinateRing
  let : Algebra (Base 1) A := Algebra.compHom A (algebraMap (Base 1) (Away 1 3))
  let : IsScalarTower (Base 1) (Away 1 3) A := by
    exact IsScalarTower.of_algebraMap_eq' (R := Base 1) (S := Away 1 3) (A := A) rfl
  let : Module.Projective (Away 1 3) A := inferInstance
  let e : ℚ_[3] ⊗[ℤ_[3]] B ≃ₐc[ℚ_[3]] ℚ_[3] ⊗[Away 1 3] A :=
    awayThreeLocalComparison W hur h3
  let P := hopfModulePatch 3 1 A B e
  let H := hopfIntersection 3 1 A B e
  letI := hopfIntersectionHopfAlgebra 3 1 A B e P
  let : HopfAlgebra.IsFiniteFlat (Base 1) H := hopfIntersectionFiniteFlat 3 1 A B e P
  let : Coalgebra.IsCocomm (Base 1) H := hopfIntersectionCocomm 3 1 A B e P
  let E₀ : Away 1 3 ⊗[Base 1] H ≃ₐc[Away 1 3] A :=
    hopfIntersectionAwayBialgEquiv 3 1 A B e P
  let E₁ : ℚ ⊗[Away 1 3] (Away 1 3 ⊗[Base 1] H) ≃ₐc[ℚ]
      ℚ ⊗[Away 1 3] A := by
    exact bialgebraBaseChangeEquiv (Away 1 3) ℚ (Away 1 3 ⊗[Base 1] H) A E₀
  let E₂ : ℚ ⊗[Away 1 3] A ≃ₐc[ℚ] W.GenericCoordinateAlgebra :=
    M.toHasFiniteFlatModel.genericBialgEquiv.symm
  let E : ℚ ⊗[Base 1] H ≃ₐc[ℚ] W.GenericCoordinateAlgebra :=
    ((bialgebraCancelBaseChange (Base 1) (Away 1 3) ℚ H).symm.trans E₁).trans E₂
  let J := ℤ ⊗[Base 1] H
  let : HopfAlgebra.IsFiniteFlat ℤ J := ⟨⟩
  let Eℤ : ℚ ⊗[ℤ] J ≃ₐc[ℚ] W.GenericCoordinateAlgebra :=
    (bialgebraCancelBaseChange (Base 1) ℤ ℚ H).trans E
  exact { toHasFiniteFlatModel := HasFiniteFlatModel.ofGenericBialgEquiv W J Eℤ }

end PadicPatching

/-- Existence of a global finite-flat model over the integers. -/
theorem global_model_over_int (W : FiniteContinuousGaloisModule)
    (h3 : HasFiniteFlatModel ℤ_[3] W.localAtThree)
    (hur : UnramifiedOutside {3} W) : Nonempty (ModelOverInt W) :=
  ⟨PadicPatching.globalModelOverInt W h3 hur⟩

end ThreeAdicPlan
