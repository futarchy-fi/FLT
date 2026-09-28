/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudIntegralFiltration
public import Mathlib.GroupTheory.Index

/-!
# Filtrations of finite flat models by order-three layers

A filtration is a chain of closed immersions of finite flat models, starting
with the trivial group, whose successive generic quotients have order three.
The quotient order is the index of the image on geometric generic points.
This definition does not assume rigidity, integral splitting, or an integral
extension of any generic morphism.

Flat closure transports such a filtration across any generic isomorphism.
In particular the graph closure has a filtration whenever the source does.
This is a construction of the subgroups needed for dévissage; it does not
assert exactness of integral quotient sequences.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/-- A length `n` chain of finite flat closed subgroups, with trivial bottom
and order-three geometric generic subquotients. -/
def FF.HasOrderThreeFiltration : FF R K → ℕ → Prop
  | X, 0 => Nat.card X.Points = 1
  | X, n + 1 => ∃ S : FF R K, ∃ i : ModelHom S X,
      Function.Surjective i ∧ Function.Injective (genericHom i) ∧
      (genericHom i).toAddMonoidHom.range.index = 3 ∧ S.HasOrderThreeFiltration n

/-- An injective generic map identifies the cardinality of its source with its image. -/
theorem GenericGaloisHom.card_range {X Y : FF R K} (i : GenericGaloisHom X Y)
    (hi : Function.Injective i) : Nat.card i.toAddMonoidHom.range = Nat.card X.Points := by
  exact Nat.card_congr (Equiv.ofBijective
    (fun x : X.Points ↦ (⟨i x, ⟨x, rfl⟩⟩ : i.toAddMonoidHom.range))
    ⟨fun x y h ↦ hi (congrArg Subtype.val h), fun ⟨_, x, hx⟩ ↦
      ⟨x, Subtype.ext hx⟩⟩).symm

/-- A closed subgroup of generic index three multiplies the order by three. -/
theorem GenericGaloisHom.card_eq_mul_three {X Y : FF R K} (i : GenericGaloisHom X Y)
    (hi : Function.Injective i) (hindex : i.toAddMonoidHom.range.index = 3) :
    Nat.card Y.Points = Nat.card X.Points * 3 := by
  rw [← i.toAddMonoidHom.range.card_mul_index, i.card_range hi, hindex]

/-- A filtration of length `n` has order `3 ^ n`. -/
theorem FF.HasOrderThreeFiltration.card {X : FF R K} {n : ℕ}
    (h : X.HasOrderThreeFiltration n) : Nat.card X.Points = 3 ^ n := by
  induction n generalizing X with
  | zero => exact h
  | succ n ih =>
    obtain ⟨S, i, _, hi, hindex, hS⟩ := h
    rw [(genericHom i).card_eq_mul_three hi hindex, ih hS, pow_succ]

/-- Every filtered model is killed by a power of three. -/
theorem FF.HasOrderThreeFiltration.killedByPowerOf {X : FF R K} {n : ℕ}
    (h : X.HasOrderThreeFiltration n) : KilledByPowerOf 3 X := by
  refine ⟨n, fun x ↦ ?_⟩
  rw [← h.card]
  exact card_nsmul_eq_zero'

variable [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]

/-- Transport a filtration to any generically isomorphic model by taking flat
closures of its subgroups. No integral inverse of the generic isomorphism is used. -/
theorem FF.HasOrderThreeFiltration.of_generic_bijective {X Y : FF R K} {n : ℕ}
    (h : X.HasOrderThreeFiltration n) (e : GenericGaloisHom X Y)
    (he : Function.Bijective e) : Y.HasOrderThreeFiltration n := by
  induction n generalizing X Y with
  | zero =>
    change Nat.card Y.Points = 1
    exact (Nat.card_congr (Equiv.ofBijective e he).symm).trans h
  | succ n ih =>
    obtain ⟨S, i, _, hi, hindex, hS⟩ := h
    let j : GenericGaloisHom S Y := e.comp (genericHom i)
    have hj : Function.Injective j := he.1.comp hi
    let T : FF R K := j.closure hj
    let t : ModelHom T Y := j.closureInclusion hj
    have ht : genericHom t = j := by
      ext x
      exact j.genericHom_closureInclusion hj x
    let s : GenericGaloisHom S T :=
      { toFun := id
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    refine ⟨T, t, Ideal.Quotient.mk_surjective, ?_, ?_, ih hS s Function.bijective_id⟩
    · simpa only [ht] using hj
    · have hcard : Nat.card Y.Points = Nat.card X.Points :=
        Nat.card_congr (Equiv.ofBijective e he).symm
      rw [ht]
      apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := S.Points))
      calc
        Nat.card S.Points * j.toAddMonoidHom.range.index = Nat.card Y.Points := by
          rw [← j.card_range hj]
          exact j.toAddMonoidHom.range.card_mul_index
        _ = Nat.card S.Points * 3 :=
          hcard.trans ((genericHom i).card_eq_mul_three hi hindex)

/-- The graph closure carries the source's order-three filtration. -/
theorem GenericGaloisHom.graphClosure_hasOrderThreeFiltration {X Y : FF R K}
    (f : GenericGaloisHom X Y) {n : ℕ} (h : X.HasOrderThreeFiltration n) :
    f.graphClosure.HasOrderThreeFiltration n := by
  let e : GenericGaloisHom X f.graphClosure :=
    { toFun := id
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact h.of_generic_bijective e Function.bijective_id

end ThreeAdicPlan
