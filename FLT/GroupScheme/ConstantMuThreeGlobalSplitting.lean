/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantFiniteFlat
public import FLT.GroupScheme.EtaleBaseChangeTower
public import FLT.GroupScheme.EtaleGroupAlgebra
public import FLT.GroupScheme.FiniteFlatRestrictedScalarExtension
public import FLT.GroupScheme.ZInvTwoSplittingDescent

/-!
# Integral splitting of generically split constant-three extensions of `μ₃`

A prescribed rational splitting of the actual extension over `ℤ[1/2]`
extends uniquely to its integral maps. Away étaleness and the three-adic
filtrations are proved for the original scalar extensions.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

open PadicPatching

local instance : Fact (¬ (3 : ℤ) ∣ 2) := ⟨by norm_num⟩

/-- The geometric generic fibre of the constant group has order three. -/
theorem constantThree_card_points : Nat.card constantThree.points = 3 := by
  change Nat.card (ZMod 3) = 3
  simp

/-- The geometric generic fibre of the cube-root group has order three. -/
theorem muThree_card_points : Nat.card muThree.points = 3 := by
  let : Algebra.Etale ℚ
      (ℚ ⊗[ZInvTwo] MonoidAlgebra ZInvTwo (Multiplicative (ZMod 3))) :=
    muThree.model.genericEtale
  change Nat.card (ℚ ⊗[ZInvTwo] MonoidAlgebra ZInvTwo (Multiplicative (ZMod 3)) →ₐ[ℚ]
    AlgebraicClosure ℚ) = 3
  rw [← GaloisModule.finrank_eq_natCard_algHom ℚ (AlgebraicClosure ℚ),
    Module.finrank_baseChange,
    Module.finrank_eq_card_basis (MonoidAlgebra.basis (Multiplicative (ZMod 3)) ZInvTwo)]
  simp

/-- Inverting three makes the actual cube-root coordinate algebra étale. -/
theorem muThree_etale_away :
    Algebra.Etale (Away 2 3) (Away 2 3 ⊗[ZInvTwo] muThree.model.CoordinateRing) := by
  have h3 : IsUnit (3 : Away 2 3) := by
    simpa only [map_ofNat] using
      (IsLocalization.Away.algebraMap_isUnit (S := Away 2 3) (3 : ZInvTwo))
  let : Algebra.Etale (Away 2 3) (MonoidAlgebra (Away 2 3) (Multiplicative (ZMod 3))) :=
    MonoidAlgebra.etale_of_isUnit_card (Away 2 3) (Multiplicative (ZMod 3)) (by simpa using h3)
  exact Algebra.Etale.of_equiv
    (MonoidAlgebra.scalarTensorEquiv ZInvTwo (Away 2 3) (M := Multiplicative (ZMod 3))).symm

/-- A rational splitting of the prescribed extension lifts uniquely over
`ℤ[1/2]`, with exactly the prescribed generic retraction and section. -/
theorem FiniteFlatExtension.existsUnique_constantThree_muThree_modelSplitting
    {X : FiniteFlatObject ZInvTwo} (E : FiniteFlatExtension constantThree X muThree)
    (s : GenericSplitSequence constantThree.toFF X.toFF muThree.toFF)
    (hi : genericHom (X := constantThree.toFF) (Y := X.toFF) E.inclusion = s.inclusion)
    (hq : genericHom (X := X.toFF) (Y := muThree.toFF) E.quotient = s.projection) :
    ∃! sO : ModelSplitting (S := constantThree.toFF) (X := X.toFF) (Q := muThree.toFF)
        E.inclusion E.quotient, sO.toGenericSplitSequence = s := by
  let : Algebra.Etale ZInvTwo constantThree.model.CoordinateRing :=
    (constantEtaleModel (ZMod 3)).etale
  let := muThree_etale_away
  let : Algebra.Etale (Away 2 3) (Away 2 3 ⊗[ZInvTwo] X.toFF.CoordinateRing) :=
    E.etale_scalarExtension (Away 2 3)
  let : Algebra.Etale (Away 2 3) (Away 2 3 ⊗[ZInvTwo] muThree.toFF.CoordinateRing) :=
    muThree_etale_away
  have hX := s.scalarExtension_hasOrderThreeFiltration ℤ_[3] ℚ_[3]
    constantThree_card_points muThree_card_points
  have hQ : (muThree.toFF.scalarExtension ℤ_[3] ℚ_[3]).HasOrderThreeFiltration 1 := by
    let : Module.Free ZInvTwo muThree.toFF.CoordinateRing :=
      inferInstanceAs (Module.Free ZInvTwo (MonoidAlgebra ZInvTwo (Multiplicative (ZMod 3))))
    apply FF.hasOrderThreeFiltration_of_order_three
    rw [FF.card_scalarExtension]
    exact muThree_card_points
  exact s.existsUnique_modelSplitting_over_zInvTwo hX hQ E.inclusion E.quotient hi hq

end ThreeAdicPlan
