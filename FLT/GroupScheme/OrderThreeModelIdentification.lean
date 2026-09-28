/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.ConstantModelIdentification
public import FLT.GroupScheme.ThreeAdicModelBaseChange

/-!
# Integral identification of the trivial order-three model

An arbitrary finite-flat model over `ℤ[1/2]` with one-dimensional trivial
mod-three geometric points is the constant-three model. The map from the
constant model is integral by normality. Its coordinate injection is an
isomorphism at three by Raynaud rigidity. Three kills the global differentials,
so three-adic étaleness implies global étaleness and both point comparisons
extend to the required integral isomorphism.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ
local instance : Fact (¬ ((3 : ℕ) : ℤ) ∣ (2 : ℤ)) := ⟨by decide⟩
local instance : Algebra ZInvTwo ℤ_[3] := (PadicPatching.baseToLocal 3 2).toAlgebra

/-- The constant-three object has exactly three geometric points. -/
theorem constantThree_card : Nat.card constantThree.points = 3 := by
  change Nat.card (ZMod 3) = 3
  simp

/-- A one-dimensional mod-three point module has exactly three elements. -/
theorem point_card_three_of_finrank_one (H : FiniteFlatObject ZInvTwo)
    [Module (ZMod 3) H.points] (hdim : Module.finrank (ZMod 3) H.points = 1) :
    Nat.card H.points = 3 :=
  (Nat.card_congr (constantThreePointEquiv H hdim).toEquiv).trans constantThree_card

/-- The given mod-three module structure annihilates all geometric points by three. -/
theorem points_killedBy_three (H : FiniteFlatObject ZInvTwo) [Module (ZMod 3) H.points] :
    KilledBy 3 H.toFF := by
  change ∀ x : H.points, (3 : ℕ) • x = 0
  intro x
  calc
    (3 : ℕ) • x = (3 : ZMod 3) • x := (Nat.cast_smul_eq_nsmul (ZMod 3) 3 x).symm
    _ = 0 := by rw [show (3 : ZMod 3) = 0 by decide, zero_smul]

/-- Trivial one-dimensional mod-three points force the actual integral model
of order three over `ℤ[1/2]` to be étale. -/
theorem etale_of_trivial_order_three (H : FiniteFlatObject ZInvTwo)
    [Module (ZMod 3) H.points] (hdim : Module.finrank (ZMod 3) H.points = 1)
    (htriv : ∀ (σ : Γ) (x : H.points), σ • x = x) :
    Algebra.Etale ZInvTwo H.model.CoordinateRing := by
  obtain ⟨f, hf, _⟩ := exists_constantThree_hom_of_trivial H hdim htriv
  let : Algebra.Etale ZInvTwo constantThree.model.CoordinateRing := constantThree_etale
  let : Algebra.Etale ℤ_[3] (ℤ_[3] ⊗[ZInvTwo] H.toFF.CoordinateRing) :=
    FiniteFlatObject.threeAdic_etale_of_injective (H := H) (J := constantThree)
      (point_card_three_of_finrank_one H hdim) constantThree_card f hf
  exact H.toFF.etale_of_etale_threeAdic_baseChange (points_killedBy_three H)

/-- A finite-flat model with one-dimensional trivial mod-three points is integrally
isomorphic to `constantThree`, compatibly with the chosen point equivalence. -/
theorem exists_iso_constantThree (H : FiniteFlatObject ZInvTwo)
    [Module (ZMod 3) H.points] (hdim : Module.finrank (ZMod 3) H.points = 1)
    (htriv : ∀ (σ : Γ) (x : H.points), σ • x = x) :
    ∃ i : H.Iso constantThree,
      ∀ x, FiniteFlatObject.pointMap i.toBialgHom x = constantThreePointEquiv H hdim x := by
  let := etale_of_trivial_order_three H hdim htriv
  exact exists_iso_constantThree_of_etale H hdim htriv

/-- Fixing the geometric point comparison makes the integral isomorphism unique. -/
theorem existsUnique_iso_constantThree (H : FiniteFlatObject ZInvTwo)
    [Module (ZMod 3) H.points] (hdim : Module.finrank (ZMod 3) H.points = 1)
    (htriv : ∀ (σ : Γ) (x : H.points), σ • x = x) :
    ∃! i : H.Iso constantThree,
      ∀ x, FiniteFlatObject.pointMap i.toBialgHom x = constantThreePointEquiv H hdim x := by
  obtain ⟨i, hi⟩ := exists_iso_constantThree H hdim htriv
  refine ⟨i, hi, fun j hj ↦ ?_⟩
  apply BialgEquiv.toBialgHom_injective
  apply FiniteFlatObject.pointMap_injective H constantThree
  ext x
  exact (hj x).trans (hi x).symm

end ThreeAdicPlan
