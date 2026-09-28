/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudLayerDescent
public import FLT.GroupScheme.RaynaudOrderNineExtension

/-!
# Raynaud rigidity for order-three filtrations of arbitrary length

Induction on the filtration makes every generically invertible integral map
invertible. At each step the subgroup comparison uses the induction hypothesis,
and the quotient comparison uses order-three rigidity. Applying this to the
graph projection extends every generic morphism uniquely, with arbitrary target.

The filtration is a genuine hypothesis: a three-primary Galois module need not
have a Galois-stable subgroup of order three.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- Every integral map from the trivial generic group is surjective on coordinates. -/
theorem ModelHom.surjective_of_order_one {X Y : FF ℤ_[3] ℚ_[3]}
    (g : ModelHom X Y) (hX : Nat.card X.Points = 1) : Function.Surjective g := by
  let : Module.Free ℤ_[3] X.CoordinateRing := Module.free_of_flat_of_isLocalRing
  obtain ⟨e⟩ := Module.nonempty_algEquiv_iff_finrank_eq_one.mpr
    ((RankThree.model_finrank X).trans hX)
  intro x
  obtain ⟨r, hr⟩ := e.surjective x
  have he : e r = algebraMap ℤ_[3] X.CoordinateRing r := e.commutes r
  exact ⟨algebraMap ℤ_[3] Y.CoordinateRing r,
    (g.toAlgHom.commutes r).trans (he.symm.trans hr)⟩

/-- A generically invertible integral map from a model with an order-three
filtration is surjective on coordinate rings, for every filtration length. -/
theorem ModelHom.surjective_of_orderThreeFiltration
    {n : ℕ} {X Y : FF ℤ_[3] ℚ_[3]} (hX : X.HasOrderThreeFiltration n)
    (g : ModelHom X Y) (hg : Function.Bijective (genericHom g)) :
    Function.Surjective g := by
  induction n generalizing X Y with
  | zero => exact g.surjective_of_order_one hX
  | succ n ih =>
    obtain ⟨S, i, _, hi, hindex, hS⟩ := hX
    let j := genericHom i
    obtain ⟨Q, q, hq, hexact, hQ⟩ := j.exists_exact_quotient
    have hQ3 : Nat.card Q.Points = 3 := hQ.trans hindex
    let e := Equiv.ofBijective (genericHom g) hg
    let inv : GenericGaloisHom Y X :=
      (genericHom g).inverse e.symm e.symm_apply_apply e.apply_symm_apply
    let q' : GenericGaloisHom Y Q := q.comp inv
    have hq' : Function.Surjective q' := hq.comp e.symm.surjective
    let h : GenericGaloisHom Q Q :=
      { toFun := id
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have hc : q'.comp (genericHom g) = h.comp q := by
      ext x
      change q (e.symm (e x)) = q x
      rw [e.symm_apply_apply]
    have hj : Function.Injective ((genericHom g).comp j) := hg.1.comp hi
    apply j.middle_surjective_of_order_three_quotient q q' hi hq hq' hexact g hj
      h hc Function.surjective_id hQ3 hQ3
    let s : GenericGaloisHom S (j.closure hi) :=
      { toFun := id
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    apply ih (hS.of_generic_bijective s Function.bijective_id)
      (j.closureMap hi g hj)
    constructor
    · intro x y he
      simpa only [j.genericHom_closureMap hi g hj] using he
    · intro x
      exact ⟨x, j.genericHom_closureMap hi g hj x⟩

/-- A generically invertible integral map between filtered models is an integral
isomorphism; only the source needs a specified filtration. -/
theorem ModelHom.bijective_of_orderThreeFiltration
    {n : ℕ} {X Y : FF ℤ_[3] ℚ_[3]} (hX : X.HasOrderThreeFiltration n)
    (g : ModelHom X Y) (hg : Function.Bijective (genericHom g)) :
    Function.Bijective g :=
  ⟨g.injective_of_baseChange_injective (g.baseChange_bijective hg).1,
    g.surjective_of_orderThreeFiltration hX hg⟩

/-- The first graph projection is surjective for any finite order-three filtration. -/
theorem GenericGaloisHom.graphFst_surjective_of_orderThreeFiltration
    {n : ℕ} {X Y : FF ℤ_[3] ℚ_[3]} (f : GenericGaloisHom X Y)
    (hX : X.HasOrderThreeFiltration n) : Function.Surjective f.graphFst := by
  apply f.graphFst.surjective_of_orderThreeFiltration
    (f.graphClosure_hasOrderThreeFiltration hX)
  constructor
  · intro x y he
    simpa only [f.genericHom_graphFst] using he
  · intro x
    exact ⟨x, f.genericHom_graphFst x⟩

/-- Every generic morphism from a model with an order-three filtration of any
length extends uniquely, without a splitting assumption or a bound on the target. -/
theorem raynaud_extend_generic_morphism_of_orderThreeFiltration
    {n : ℕ} (X Y : FF ℤ_[3] ℚ_[3]) (hX : X.HasOrderThreeFiltration n)
    (f : GenericGaloisHom X Y) : ∃! fO : ModelHom X Y, genericHom fO = f :=
  raynaud_extend_generic_morphism_of_graphFst_surjective X Y f
    (f.graphFst_surjective_of_orderThreeFiltration hX)

end ThreeAdicPlan
