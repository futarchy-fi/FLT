/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.FiniteFlatIso
public import FLT.GroupScheme.ThreeTorsionEtaleDescent

/-!
# Three-adic rigidity for global order-three models

The actual scalar extension of a global coordinate Hopf algebra is a three-adic
finite-flat model. Its geometric point count is unchanged, as follows from the
coordinate rank. Raynaud's order-three rigidity therefore makes every injective
map between global order-three coordinate algebras bijective after this base change.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

local instance : Fact (¬ ((3 : ℕ) : ℤ) ∣ (2 : ℤ)) := ⟨by decide⟩
local instance : Algebra ZInvTwo ℤ_[3] := (PadicPatching.baseToLocal 3 2).toAlgebra

local instance : Algebra ZInvTwo ℚ_[3] :=
  Algebra.compHom ℚ_[3] (PadicPatching.baseToLocal 3 2)
local instance : IsScalarTower ZInvTwo ℤ_[3] ℚ_[3] :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance : IsScalarTower ZInvTwo ℚ ℚ_[3] := by
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext (Submonoid.powers (2 : ℤ))
  exact Subsingleton.elim _ _

/-- The generic three-adic algebra of the integral scalar extension is the
scalar extension of the original rational generic algebra. -/
def FiniteFlatObject.threeAdicGenericEquiv (H : FiniteFlatObject ZInvTwo) :
    ℚ_[3] ⊗[ℤ_[3]] (ℤ_[3] ⊗[ZInvTwo] H.model.CoordinateRing) ≃ₐc[ℚ_[3]]
      ℚ_[3] ⊗[ℚ] (ℚ ⊗[ZInvTwo] H.model.CoordinateRing) :=
  (bialgebraCancelBaseChange ZInvTwo ℤ_[3] ℚ_[3] H.model.CoordinateRing).trans
    (bialgebraCancelBaseChange ZInvTwo ℚ ℚ_[3] H.model.CoordinateRing).symm

/-- The actual integral three-adic scalar extension, with its geometric points. -/
def FiniteFlatObject.threeAdicBaseChange (H : FiniteFlatObject ZInvTwo) : FF ℤ_[3] ℚ_[3] := by
  let A := ℤ_[3] ⊗[ZInvTwo] H.model.CoordinateRing
  let : HopfAlgebra.IsFiniteFlat ℤ_[3] A := ⟨⟩
  let : Algebra.Etale ℚ_[3] (ℚ_[3] ⊗[ℤ_[3]] A) :=
    Algebra.Etale.of_equiv H.threeAdicGenericEquiv.symm.toAlgEquiv
  letI := HopfAlgebra.pointsCommGroup ℚ_[3] (AlgebraicClosure ℚ_[3])
    (ℚ_[3] ⊗[ℤ_[3]] A)
  exact
    { CoordinateRing := A
      Points := Additive (ℚ_[3] ⊗[ℤ_[3]] A →ₐ[ℚ_[3]] AlgebraicClosure ℚ_[3])
      points :=
        { toFun := id
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      points_bijective := Function.bijective_id }

/-- Scalar extension preserves the order of a global finite-flat model. -/
theorem FiniteFlatObject.threeAdicBaseChange_card (H : FiniteFlatObject ZInvTwo) :
    Nat.card H.threeAdicBaseChange.Points = Nat.card H.points := by
  rw [← RankThree.model_finrank]
  change Module.finrank ℤ_[3] (ℤ_[3] ⊗[ZInvTwo] H.model.CoordinateRing) = _
  rw [Module.finrank_baseChange, ← Module.finrank_baseChange (R := ℚ)]
  exact (H.toFF.genericCoordinates.toAlgEquiv.toLinearEquiv.finrank_eq).symm.trans
    (GaloisModule.finrank_equivariantFunctions ℚ (AlgebraicClosure ℚ) H.points)

/-- Injective maps between global order-three models become isomorphisms over `ℤ₃`. -/
theorem FiniteFlatObject.threeAdic_map_bijective {H J : FiniteFlatObject ZInvTwo}
    (hH : Nat.card H.points = 3) (hJ : Nat.card J.points = 3)
    (f : H.model.CoordinateRing →ₐc[ZInvTwo] J.model.CoordinateRing)
    (hf : Function.Injective f) :
    Function.Bijective (Bialgebra.TensorProduct.map (BialgHom.id ℤ_[3] ℤ_[3]) f) := by
  let : FaithfulSMul ZInvTwo ℤ_[3] := by
    apply (faithfulSMul_iff_algebraMap_injective ZInvTwo ℤ_[3]).mpr
    apply IsLocalization.injective_of_map_algebraMap_zero
      (M := Submonoid.powers (2 : ℤ)) ZInvTwo (algebraMap ZInvTwo ℤ_[3])
    intro n hn
    have hn0 : n = 0 := by
      have hn' : (n : ℤ_[3]) = 0 := by simpa using hn
      exact_mod_cast hn'
    simp [hn0]
  let : Module.Flat ZInvTwo ℤ_[3] := inferInstance
  let g : H.threeAdicBaseChange.CoordinateRing →ₐc[ℤ_[3]]
      J.threeAdicBaseChange.CoordinateRing :=
    Bialgebra.TensorProduct.map (BialgHom.id ℤ_[3] ℤ_[3]) f
  have hg : Function.Injective g := by
    exact Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  exact ⟨hg, raynaud_integral_rigidity_of_order_three H.threeAdicBaseChange
    J.threeAdicBaseChange (H.threeAdicBaseChange_card.trans hH)
    (J.threeAdicBaseChange_card.trans hJ) g hg⟩

/-- An order-three model embedded into an integral étale order-three model is
étale after scalar extension to the three-adic integers. -/
theorem FiniteFlatObject.threeAdic_etale_of_injective {H J : FiniteFlatObject ZInvTwo}
    (hH : Nat.card H.points = 3) (hJ : Nat.card J.points = 3)
    [Algebra.Etale ZInvTwo J.model.CoordinateRing]
    (f : H.model.CoordinateRing →ₐc[ZInvTwo] J.model.CoordinateRing)
    (hf : Function.Injective f) :
    Algebra.Etale ℤ_[3] (ℤ_[3] ⊗[ZInvTwo] H.model.CoordinateRing) :=
  Algebra.Etale.of_equiv (BialgEquiv.ofBijective
    (Bialgebra.TensorProduct.map (BialgHom.id ℤ_[3] ℤ_[3]) f)
    (FiniteFlatObject.threeAdic_map_bijective hH hJ f hf)).symm.toAlgEquiv

end ThreeAdicPlan
