/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudTorsorDescent
public import Mathlib.Algebra.Module.Congruence.Defs

/-!
# Rigidity for nonsplit extensions of order-three models

The first graph projection is an isomorphism for a source admitting an
order-three subgroup and quotient. Thus every generic morphism extends uniquely.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- A generic subgroup admits a finite flat quotient model, with the prescribed
kernel and generic order equal to the subgroup index. -/
theorem GenericGaloisHom.exists_exact_quotient
    {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
    {S X : FF R K} (i : GenericGaloisHom S X) :
    ∃ Q : FF R K, ∃ q : GenericGaloisHom X Q, Function.Surjective q ∧
      (∀ x, q x = 0 ↔ ∃ s, i s = x) ∧
      Nat.card Q.Points = i.toAddMonoidHom.range.index := by
  let H := i.toAddMonoidHom.range
  let c : ModuleCon (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X.Points :=
    { toAddCon := QuotientAddGroup.con H
      smul σ x y h := by
        change QuotientAddGroup.leftRel H x y at h
        change QuotientAddGroup.leftRel H (σ • x) (σ • y)
        rw [QuotientAddGroup.leftRel_eq] at h ⊢
        dsimp only at h ⊢
        rw [← smul_neg, ← smul_add]
        obtain ⟨s, hs⟩ := h
        refine ⟨σ • s, ?_⟩
        change i (σ • s) = σ • (-x + y)
        rw [map_smul]
        exact congrArg (σ • ·) hs }
  let q : X.Points →+[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K] c.Quotient :=
    { toFun := Quotient.mk''
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hq : Function.Surjective q := Quotient.mk''_surjective
  let Q := FF.ofIsFiniteFlat c.Quotient
    (X.isFiniteFlat.quotient R K (AlgebraicClosure K) X.Points q hq)
  refine ⟨Q, q, hq, ?_, ?_⟩
  · intro x
    change (QuotientAddGroup.mk' H) x = 0 ↔ ∃ s, i s = x
    rw [← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']
    rfl
  · rfl

/-- The graph projection is surjective for any extension of two order-three
point groups, whether or not that generic extension splits. -/
theorem GenericGaloisHom.graphFst_surjective_of_order_three_extension
    {S X Q Y : FF ℤ_[3] ℚ_[3]} (f : GenericGaloisHom X Y)
    (i : GenericGaloisHom S X) (q : GenericGaloisHom X Q)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x)
    (hS : Nat.card S.Points = 3) (hQ : Nat.card Q.Points = 3) :
    Function.Surjective f.graphFst := by
  let iG : GenericGaloisHom S f.graphClosure :=
    { toFun := i
      map_zero' := map_zero i
      map_add' := map_add i
      map_smul' := map_smul i }
  let qG : GenericGaloisHom f.graphClosure Q := q.comp (genericHom f.graphFst)
  have hqG : Function.Surjective qG := by
    intro y
    obtain ⟨x, hx⟩ := hq y
    exact ⟨x, by simpa [qG] using hx⟩
  have hexactG : ∀ x, qG x = 0 ↔ ∃ s, iG s = x := by
    intro x
    change q (genericHom f.graphFst x) = 0 ↔ ∃ s, i s = x
    rw [f.genericHom_graphFst]
    exact hexact x
  have hj : Function.Injective ((genericHom f.graphFst).comp iG) := by
    intro a b h
    change genericHom f.graphFst (i a) = genericHom f.graphFst (i b) at h
    rw [f.genericHom_graphFst, f.genericHom_graphFst] at h
    exact hi h
  let h : GenericGaloisHom Q Q :=
    { toFun := id
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact iG.middle_surjective_of_order_three_layers qG q hi hqG hq hexactG hS
    f.graphFst hj h (by ext; rfl) Function.surjective_id hQ hQ

/-- Generic morphisms from nonsplit order-nine extensions extend uniquely. -/
theorem raynaud_extend_generic_morphism_of_order_three_extension
    {S X Q : FF ℤ_[3] ℚ_[3]} (i : GenericGaloisHom S X) (q : GenericGaloisHom X Q)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x)
    (hS : Nat.card S.Points = 3) (hQ : Nat.card Q.Points = 3)
    (Y : FF ℤ_[3] ℚ_[3]) (f : GenericGaloisHom X Y) :
    ∃! fO : ModelHom X Y, genericHom fO = f :=
  raynaud_extend_generic_morphism_of_graphFst_surjective X Y f
    (f.graphFst_surjective_of_order_three_extension i q hi hq hexact hS hQ)

/-- An order-nine model with an order-three generic subgroup has a surjective
first graph projection. The subgroup is replaced by its integral flat closure. -/
theorem GenericGaloisHom.graphFst_surjective_of_order_nine
    {S X Y : FF ℤ_[3] ℚ_[3]} (f : GenericGaloisHom X Y)
    (hX : Nat.card X.Points = 9) (i : GenericGaloisHom S X)
    (hi : Function.Injective i) (hS : Nat.card S.Points = 3) :
    Function.Surjective f.graphFst := by
  obtain ⟨Q, q, hq, hexact, hQ⟩ := i.exists_exact_quotient
  have hindex := i.toAddMonoidHom.range.card_mul_index
  rw [i.card_range hi, hS, hX] at hindex
  have hQ3 : Nat.card Q.Points = 3 := by omega
  exact f.graphFst_surjective_of_order_three_extension i q hi hq hexact hS hQ3

/-- An order-three subgroup suffices for unique integral extension from an
order-nine model, including nonsplit models. -/
theorem raynaud_extend_generic_morphism_of_order_nine
    {S X : FF ℤ_[3] ℚ_[3]} (hX : Nat.card X.Points = 9)
    (i : GenericGaloisHom S X) (hi : Function.Injective i) (hS : Nat.card S.Points = 3)
    (Y : FF ℤ_[3] ℚ_[3]) (f : GenericGaloisHom X Y) :
    ∃! fO : ModelHom X Y, genericHom fO = f :=
  raynaud_extend_generic_morphism_of_graphFst_surjective X Y f
    (f.graphFst_surjective_of_order_nine hX i hi hS)

/-- A length-two order-three filtration suffices for graph rigidity. -/
theorem GenericGaloisHom.graphFst_surjective_of_order_three_filtration
    {X Y : FF ℤ_[3] ℚ_[3]} (f : GenericGaloisHom X Y)
    (hX : X.HasOrderThreeFiltration 2) : Function.Surjective f.graphFst := by
  obtain ⟨S, i, _, hi, hindex, hS⟩ := hX
  obtain ⟨Q, q, hq, hexact, hQ⟩ := (genericHom i).exists_exact_quotient
  exact f.graphFst_surjective_of_order_three_extension (genericHom i) q hi hq hexact
    hS.card (hQ.trans hindex)

/-- Every generic morphism from a length-two order-three filtration extends uniquely. -/
theorem raynaud_extend_generic_morphism_of_order_three_filtration
    (X Y : FF ℤ_[3] ℚ_[3]) (hX : X.HasOrderThreeFiltration 2)
    (f : GenericGaloisHom X Y) : ∃! fO : ModelHom X Y, genericHom fO = f :=
  raynaud_extend_generic_morphism_of_graphFst_surjective X Y f
    (f.graphFst_surjective_of_order_three_filtration hX)

end ThreeAdicPlan
