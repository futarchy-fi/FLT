/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.BialgebraBaseChange
public import FLT.GroupScheme.GenericFieldChange
public import FLT.GroupScheme.IntegralEtaleModel
public import FLT.GroupScheme.PadicHopfPatching
/-!
# Global finite-flat models away from two

An étale model over the ring with two and three inverted is patched with a
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
local instance : Fact (¬ (3 : ℤ) ∣ 2) := ⟨by norm_num⟩
/-- The excluded integers are prime. -/
local instance : Fact (∀ p ∈ ({2, 3} : Finset ℕ), p.Prime) :=
  ⟨by simp [Nat.prime_two, Nat.prime_three]⟩

/-- The two presentations of the ring with two and three inverted agree. -/
def awayTwoThreeEquiv : ZInvPrimes {2, 3} ≃ₐ[ℤ] Away 2 3 := by
  convert (awayEquivSingle 3 2).symm using 1
  norm_num [ZInvPrimes]

/-- The away ring is an algebra over its single-localization presentation. -/
local instance : Algebra (ZInvPrimes {2, 3}) (Away 2 3) :=
  awayTwoThreeEquiv.toRingEquiv.toRingHom.toAlgebra

/-- The canonical rational embedding of the away coefficient ring. -/
local instance : Algebra (Away 2 3) ℚ :=
  (IsLocalization.Away.lift (3 : Base 2)
    (show IsUnit (algebraMap (Base 2) ℚ 3) by
      rw [map_ofNat]
      exact isUnit_iff_ne_zero.mpr (show (3 : ℚ) ≠ 0 by decide))).toAlgebra

/-- Maps out of an integer localization give compatible scalar towers. -/
theorem integerLocalizationScalarTower (n : ℤ) (R S T : Type)
    [CommRing R] [CommRing S] [CommRing T] [Algebra ℤ R]
    [IsLocalization.Away n R] [Algebra R S] [Algebra S T] [Algebra R T] :
    IsScalarTower R S T := by
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext (Submonoid.powers n)
  ext
  simp

/-- The single localization acts on the local field through the rationals. -/
local instance : Algebra (ZInvPrimes {2, 3}) ℚ_[3] :=
  Algebra.compHom ℚ_[3] (algebraMap (ZInvPrimes {2, 3}) ℚ)
/-- The coefficient embeddings form a compatible scalar tower. -/
local instance : IsScalarTower (ZInvPrimes {2, 3}) ℚ ℚ_[3] :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The coefficient embeddings form a compatible scalar tower. -/
local instance : IsScalarTower (Base 2) (Away 2 3) ℚ :=
  by exact integerLocalizationScalarTower 2 (Base 2) (Away 2 3) ℚ
/-- The coefficient embeddings form a compatible scalar tower. -/
local instance : IsScalarTower (Base 2) ℚ ℚ_[3] :=
  by exact integerLocalizationScalarTower 2 _ _ _
/-- The coefficient embeddings form a compatible scalar tower. -/
local instance : IsScalarTower (Away 2 3) ℚ ℚ_[3] :=
  integerLocalizationScalarTower ((2 : ℤ) * (3 : ℕ)) _ _ _
/-- The coefficient embeddings form a compatible scalar tower. -/
local instance : IsScalarTower (ZInvPrimes {2, 3}) (Away 2 3) ℚ :=
  integerLocalizationScalarTower (∏ p ∈ ({2, 3} : Finset ℕ), (p : ℤ)) _ _ _
/-- The coefficient embeddings form a compatible scalar tower. -/
local instance : IsScalarTower (ZInvPrimes {2, 3}) (Away 2 3) ℚ_[3] :=
  integerLocalizationScalarTower (∏ p ∈ ({2, 3} : Finset ℕ), (p : ℤ)) _ _ _

/-- The model away from two and three, presented over the iterated localization
used by arithmetic patching. -/
def awayTwoModel (W : FiniteContinuousGaloisModule)
    (hur : UnramifiedOutside {2, 3} W) : FiniteEtaleModel (Away 2 3) W := by
  let I := W.integralEtaleModel {2, 3} hur
  let A := Away 2 3 ⊗[ZInvPrimes {2, 3}] I.CoordinateRing
  let : HopfAlgebra.IsFiniteFlat (Away 2 3) A := ⟨⟩
  let E : ℚ ⊗[Away 2 3] A ≃ₐc[ℚ] W.GenericCoordinateAlgebra :=
    (bialgebraCancelBaseChange (ZInvPrimes {2, 3}) (Away 2 3) ℚ I.CoordinateRing).trans
      (W.integralEtaleModelGenericEquiv {2, 3} hur)
  exact { toHasFiniteFlatModel := HasFiniteFlatModel.ofGenericBialgEquiv W A E
          etale := by change Algebra.Etale (Away 2 3) A; infer_instance }

/-- The away and local models have the same local generic bialgebra. -/
def awayTwoLocalComparison (W : FiniteContinuousGaloisModule)
    (hur : UnramifiedOutside {2, 3} W) (h3 : HasFiniteFlatModel ℤ_[3] W.localAtThree) :
    ℚ_[3] ⊗[ℤ_[3]] h3.CoordinateRing ≃ₐc[ℚ_[3]]
      ℚ_[3] ⊗[Away 2 3] (awayTwoModel W hur).CoordinateRing :=
  (W.localModelGenericBialgEquiv h3).symm.trans
    ((bialgebraBaseChangeEquiv ℚ ℚ_[3] _ _
      (awayTwoModel W hur).toHasFiniteFlatModel.genericBialgEquiv).trans
        (bialgebraCancelBaseChange (Away 2 3) ℚ ℚ_[3]
          (awayTwoModel W hur).CoordinateRing))

/-- A local finite-flat model at three glues to the étale model away from two
and three, producing a finite-flat model over `ℤ[1/2]`. -/
def globalModelAwayTwo (W : FiniteContinuousGaloisModule)
    (h3 : HasFiniteFlatModel ℤ_[3] W.localAtThree)
    (hur : UnramifiedOutside {2, 3} W) : ModelOverZInvTwo W := by
  let M := awayTwoModel W hur
  let A := M.CoordinateRing
  let B := h3.CoordinateRing
  let : Algebra (Base 2) A := Algebra.compHom A (algebraMap (Base 2) (Away 2 3))
  let : IsScalarTower (Base 2) (Away 2 3) A := by
    exact IsScalarTower.of_algebraMap_eq' (R := Base 2) (S := Away 2 3) (A := A) rfl
  let : Module.Projective (Away 2 3) A := inferInstance
  let e : ℚ_[3] ⊗[ℤ_[3]] B ≃ₐc[ℚ_[3]] ℚ_[3] ⊗[Away 2 3] A :=
    awayTwoLocalComparison W hur h3
  let P := hopfModulePatch 3 2 A B e
  let H := hopfIntersection 3 2 A B e
  letI := hopfIntersectionHopfAlgebra 3 2 A B e P
  let : HopfAlgebra.IsFiniteFlat (Base 2) H := hopfIntersectionFiniteFlat 3 2 A B e P
  let : Coalgebra.IsCocomm (Base 2) H := hopfIntersectionCocomm 3 2 A B e P
  let E₀ : Away 2 3 ⊗[Base 2] H ≃ₐc[Away 2 3] A :=
    hopfIntersectionAwayBialgEquiv 3 2 A B e P
  let E₁ : ℚ ⊗[Away 2 3] (Away 2 3 ⊗[Base 2] H) ≃ₐc[ℚ]
      ℚ ⊗[Away 2 3] A := by
    exact bialgebraBaseChangeEquiv (Away 2 3) ℚ (Away 2 3 ⊗[Base 2] H) A E₀
  let E₂ : ℚ ⊗[Away 2 3] A ≃ₐc[ℚ] W.GenericCoordinateAlgebra :=
    M.toHasFiniteFlatModel.genericBialgEquiv.symm
  let E : ℚ ⊗[Base 2] H ≃ₐc[ℚ] W.GenericCoordinateAlgebra :=
    ((bialgebraCancelBaseChange (Base 2) (Away 2 3) ℚ H).symm.trans E₁).trans E₂
  exact { toHasFiniteFlatModel := HasFiniteFlatModel.ofGenericBialgEquiv W H E }

end PadicPatching

/-- Existence of a global finite-flat model away from two. -/
theorem global_model_away_two (W : FiniteContinuousGaloisModule)
    (h3 : HasFiniteFlatModel ℤ_[3] W.localAtThree)
    (hur : UnramifiedOutside {2, 3} W) : Nonempty (ModelOverZInvTwo W) :=
  ⟨PadicPatching.globalModelAwayTwo W h3 hur⟩

end ThreeAdicPlan
