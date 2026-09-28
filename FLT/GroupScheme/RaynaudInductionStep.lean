/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudLayerDescent
public import FLT.GroupScheme.RaynaudOrderNineExtension

/-!
# The order-three-kernel step in Raynaud induction

Given a Galois-stable subgroup of order three, rigidity at strictly smaller
orders implies graph rigidity, hence unique extension of every generic morphism.
The quotient is constructed, and its order is proved smaller than the source.
The induction hypothesis is never applied to the source itself.

This is a conditional induction step, not the unrestricted Raynaud theorem:
existence of a Galois-stable order-three subgroup is a separate hypothesis.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- A generic quotient by an order-three subgroup has strictly smaller order. -/
theorem GenericGaloisHom.card_quotient_lt_of_order_three
    {S X Q : FF ℤ_[3] ℚ_[3]} (i : GenericGaloisHom S X) (q : GenericGaloisHom X Q)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x) (hS : Nat.card S.Points = 3) :
    Nat.card Q.Points < Nat.card X.Points := by
  have hm := i.toAddMonoidHom.range.card_mul_index
  rw [i.card_range hi, i.index_range_of_exact q hq hexact, hS] at hm
  have hp := Nat.card_pos (α := Q.Points)
  omega

/-- The single-layer graph argument uses order-three rigidity on the kernel and
an induction hypothesis only at orders strictly smaller than the source. -/
theorem GenericGaloisHom.graphFst_surjective_of_order_three_kernel
    {S X Q Y : FF ℤ_[3] ℚ_[3]} (f : GenericGaloisHom X Y)
    (i : GenericGaloisHom S X) (q : GenericGaloisHom X Q)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x) (hS : Nat.card S.Points = 3)
    (ih : ∀ (A B : FF ℤ_[3] ℚ_[3]), Nat.card A.Points < Nat.card X.Points →
      ∀ g : ModelHom A B, Function.Bijective (genericHom g) → Function.Surjective g) :
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
  have hc : q.comp (genericHom f.graphFst) = h.comp qG := by ext; rfl
  apply iG.middle_surjective_of_layer_maps qG q hi hqG hq hexactG f.graphFst hj h hc
    (iG.closureMap_bijective_of_order_three hi f.graphFst hj hS).2
  refine ⟨qG.flatQuotientMap_injective q hqG hq f.graphFst h hc Function.surjective_id, ?_⟩
  apply ih (qG.flatQuotient hqG) (q.flatQuotient hq)
    (i.card_quotient_lt_of_order_three q hi hq hexact hS)
    (qG.flatQuotientMap q hqG hq f.graphFst h hc)
  constructor
  · intro a b he
    rw [GenericGaloisHom.genericHom_flatQuotientMap,
      GenericGaloisHom.genericHom_flatQuotientMap] at he
    exact he
  · intro y
    exact ⟨y, qG.genericHom_flatQuotientMap q hqG hq f.graphFst h hc y⟩

/-- An order-three generic subgroup and rigidity at strictly smaller orders
suffice to extend every generic morphism uniquely. The finite flat quotient
and the strict order decrease are constructed inside the proof. -/
theorem raynaud_extend_generic_morphism_induction_step
    {S X : FF ℤ_[3] ℚ_[3]} (i : GenericGaloisHom S X)
    (hi : Function.Injective i) (hS : Nat.card S.Points = 3)
    (ih : ∀ (A B : FF ℤ_[3] ℚ_[3]), Nat.card A.Points < Nat.card X.Points →
      ∀ g : ModelHom A B, Function.Bijective (genericHom g) → Function.Surjective g)
    (Y : FF ℤ_[3] ℚ_[3]) (f : GenericGaloisHom X Y) :
    ∃! fO : ModelHom X Y, genericHom fO = f := by
  obtain ⟨Q, q, hq, hexact, _⟩ := i.exists_exact_quotient
  exact raynaud_extend_generic_morphism_of_graphFst_surjective X Y f
    (f.graphFst_surjective_of_order_three_kernel i q hi hq hexact hS ih)

end ThreeAdicPlan
