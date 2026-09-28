/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudModelArithmetic

/-!
# Extension from finite products of order-three models

Generic morphisms from any nonempty finite product of order-three models over
`ℤ_[3]` extend uniquely. This gives non-étale examples of arbitrarily large rank,
but does not classify arbitrary models killed by three as such products.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] [PerfectField K]

/-- Restrict a generic morphism on a product to its first factor. -/
def GenericGaloisHom.prodLeft {X Y Z : FF R K} (f : GenericGaloisHom (X.prod Y) Z) :
    GenericGaloisHom X Z where
  toFun x := f (x, 0)
  map_zero' := map_zero f
  map_add' x y := by simpa using map_add f (x, 0) (y, 0)
  map_smul' σ x := by simpa using map_smul f σ (x, 0)

/-- Restrict a generic morphism on a product to its second factor. -/
def GenericGaloisHom.prodRight {X Y Z : FF R K} (f : GenericGaloisHom (X.prod Y) Z) :
    GenericGaloisHom Y Z where
  toFun y := f (0, y)
  map_zero' := map_zero f
  map_add' x y := by simpa using map_add f (0, x) (0, y)
  map_smul' σ x := by simpa using map_smul f σ (0, x)

omit [PerfectField K] in
/-- A generic map from a product is the sum of its two restrictions. -/
theorem GenericGaloisHom.prod_decomposition {X Y Z : FF R K}
    (f : GenericGaloisHom (X.prod Y) Z) (x : X.Points) (y : Y.Points) :
    f (x, y) = f.prodLeft x + f.prodRight y := by
  change f (x, y) = f (x, 0) + f (0, y)
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using
    map_add f (x, 0) (0, y)

/-- A nonempty finite product of chosen models, with the first factor specified separately. -/
@[implicit_reducible]
def FF.productChain (X : FF R K) : List (FF R K) → FF R K
  | [] => X
  | Y :: Ys => X.prod (Y.productChain Ys)

omit [PerfectField K] in
/-- The order of a product of order-three models is the corresponding power of three. -/
theorem FF.productChain_card (X : FF R K) (Xs : List (FF R K))
    (hX : Nat.card X.Points = 3) (hXs : ∀ Y ∈ Xs, Nat.card Y.Points = 3) :
    Nat.card (X.productChain Xs).Points = 3 ^ (Xs.length + 1) := by
  induction Xs generalizing X with
  | nil => simpa [FF.productChain] using hX
  | cons Y Ys ih =>
    change Nat.card (X.Points × (Y.productChain Ys).Points) = _
    rw [Nat.card_prod, hX, ih Y (hXs Y (by simp)) (by
      intro Z hZ
      exact hXs Z (by simp [hZ]))]
    simp [pow_succ, mul_comm]

omit [PerfectField K] in
/-- Every product of order-three models is killed by three on its generic fibre. -/
theorem FF.productChain_killed (X : FF R K) (Xs : List (FF R K))
    (hX : Nat.card X.Points = 3) (hXs : ∀ Y ∈ Xs, Nat.card Y.Points = 3)
    (x : (X.productChain Xs).Points) : 3 • x = 0 := by
  induction Xs generalizing X with
  | nil =>
    rw [← hX]
    exact card_nsmul_eq_zero'
  | cons Y Ys ih =>
    apply Prod.ext
    · change 3 • x.1 = 0
      rw [← hX]
      exact card_nsmul_eq_zero'
    · exact ih Y (hXs Y (by simp))
        (by intro Z hZ; exact hXs Z (by simp [hZ])) x.2

/-- Generic morphisms from finite products of order-three models extend uniquely.
The order-three hypotheses concern the individual factors, not a classification
hypothesis on arbitrary models killed by three. -/
theorem raynaud_extend_generic_morphism_of_product_order_three
    (X : FF ℤ_[3] ℚ_[3]) (Xs : List (FF ℤ_[3] ℚ_[3]))
    (hX : Nat.card X.Points = 3) (hXs : ∀ Y ∈ Xs, Nat.card Y.Points = 3)
    (Z : FF ℤ_[3] ℚ_[3]) (f : GenericGaloisHom (X.productChain Xs) Z) :
    ∃! fO : ModelHom (X.productChain Xs) Z, genericHom fO = f := by
  induction Xs generalizing X with
  | nil => exact raynaud_extend_generic_morphism_of_order_three X Z hX f
  | cons Y Ys ih =>
    change GenericGaloisHom (X.prod (Y.productChain Ys)) Z at f
    obtain ⟨l, hl, _⟩ := raynaud_extend_generic_morphism_of_order_three X Z hX f.prodLeft
    obtain ⟨r, hr, _⟩ := ih Y (hXs Y (by simp))
      (by intro W hW; exact hXs W (by simp [hW])) f.prodRight
    let fO : ModelHom (X.prod (Y.productChain Ys)) Z :=
      ModelHom.add (X := X.prod (Y.productChain Ys)) (Y := Z)
        ((X.fst (Y.productChain Ys)).comp l) ((X.snd (Y.productChain Ys)).comp r)
    have he : genericHom fO = f := by
      ext x
      change genericHom (ModelHom.add (X := X.prod (Y.productChain Ys)) (Y := Z)
        ((X.fst (Y.productChain Ys)).comp l) ((X.snd (Y.productChain Ys)).comp r)) x = f x
      rw [ModelHom.genericHom_add, genericHom_comp, genericHom_comp,
        FF.genericHom_fst, FF.genericHom_snd, hl, hr]
      exact (f.prod_decomposition x.1 x.2).symm
    exact ⟨fO, he, fun g hg ↦ genericHom_injective _ _ (hg.trans he.symm)⟩

/-- The first graph projection is surjective for a product of order-three source models. -/
theorem GenericGaloisHom.graphFst_surjective_of_product_order_three
    (X : FF ℤ_[3] ℚ_[3]) (Xs : List (FF ℤ_[3] ℚ_[3]))
    (hX : Nat.card X.Points = 3) (hXs : ∀ Y ∈ Xs, Nat.card Y.Points = 3)
    (Z : FF ℤ_[3] ℚ_[3]) (f : GenericGaloisHom (X.productChain Xs) Z) :
    Function.Surjective f.graphFst := by
  obtain ⟨g, hg, _⟩ :=
    raynaud_extend_generic_morphism_of_product_order_three X Xs hX hXs Z f
  apply f.graphFst_surjective_of_integral
  intro z
  refine ⟨g z, ?_⟩
  rw [← hg, ModelHom.toBialgHom_genericHom]
  rfl

end ThreeAdicPlan
