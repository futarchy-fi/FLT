/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.FramedArithmeticIdeal
public import FLT.Deformations.UniversalLocalQuotient

/-!
# Arithmetic equations on the actual universal framed ring

The residual representation proves simultaneous properness. The quotient
classifies lifts with prescribed determinant, triviality and local quotient.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory IsLocalRing
namespace Deformation
open ProartinianCat
universe u
variable (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (n : Type) [Fintype n] [DecidableEq n] [Finite (ResidueField O)]
  (ρ₀ : G →ₜ* GL n (residueField (𝓞 := O)))
  (δ : G → O) (S : Set G) {H : Type u} [Group H]
  (ι : H →* G) (χ : H →* Oˣ) (q : n)

local notation "U" => profiniteFramedLimitObject O G n ρ₀
local notation "r" => profiniteUniversalLift O G n ρ₀

/-- The explicit determinant, inertia and quotient ideal of the universal ring. -/
def universalArithmeticIdeal : Ideal U := framedArithmeticIdeal U r δ S ι χ q

omit [TotallyDisconnectedSpace G] in
/-- The universal arithmetic equation ideal is closed. -/
theorem universalArithmeticIdeal_closed :
    IsClosed (universalArithmeticIdeal O G n ρ₀ δ S ι χ q : Set U) :=
  framedArithmeticIdeal_closed U r δ S ι χ q

variable (hdet : ∀ g, (ρ₀ g : Matrix n n (residueField (𝓞 := O))).det =
    algebraMap O (residueField (𝓞 := O)) (δ g))
  (htriv : ∀ g ∈ S, ρ₀ g = 1)
  (hrow : ∀ g j, ρ₀ (ι g) q j =
    if j = q then algebraMap O (residueField (𝓞 := O)) (χ g : O) else 0)

include hdet htriv hrow
omit [TotallyDisconnectedSpace G] in
/-- All three residual equations hold at the same residual point. -/
theorem universalArithmeticIdeal_ne_top :
    universalArithmeticIdeal O G n ρ₀ δ S ι χ q ≠ ⊤ := by
  let f := toResidueField U
  have hr (g : G) : Matrix.GeneralLinearGroup.map f.hom.toRingHom (r g) = ρ₀ g :=
    congrArg (fun t : G →* GL n (residueField (𝓞 := O)) ↦ t g)
      (profiniteUniversalContinuousLift_isFramedLift O G n ρ₀)
  apply framedArithmeticIdeal_ne_top U r δ S ι χ q f
  · intro g
    have hd := RingHom.map_det f.hom.toRingHom (r g).val
    exact hd.trans ((congrArg (fun M : GL n (residueField (𝓞 := O)) ↦
      (M : Matrix n n (residueField (𝓞 := O))).det) (hr g)).trans (hdet g))
  · intro g hg
    exact (hr g).trans (htriv g hg)
  · intro g j
    exact (congrArg (fun M : GL n (residueField (𝓞 := O)) ↦ M q j) (hr (ι g))).trans
      (hrow g j)

/-- The actual simultaneous quotient, with properness proved from the residual representation. -/
def universalArithmeticObject : ProartinianCat O :=
  closedIdealQuotient U (universalArithmeticIdeal O G n ρ₀ δ S ι χ q)
    (universalArithmeticIdeal_closed O G n ρ₀ δ S ι χ q)
    (universalArithmeticIdeal_ne_top O G n ρ₀ δ S ι χ q hdet htriv hrow)

/-- Maps out of the quotient are exactly lifts satisfying the three arithmetic equations. -/
def universalArithmeticEquiv (A : ProartinianCat O) :
    (universalArithmeticObject O G n ρ₀ δ S ι χ q hdet htriv hrow ⟶ A) ≃
      {τ : ContinuousFramedLifts O G n ρ₀ A //
        (∀ g, (τ.val g : Matrix n n A).det = algebraMap O A (δ g)) ∧
        (∀ g ∈ S, τ.val g = 1) ∧
        (∀ g j, τ.val (ι g) q j =
          if j = q then algebraMap O A (χ g : O) else 0)} :=
  (closedIdealFactorEquiv U (universalArithmeticIdeal O G n ρ₀ δ S ι χ q)
    (universalArithmeticIdeal_closed O G n ρ₀ δ S ι χ q)
    (universalArithmeticIdeal_ne_top O G n ρ₀ δ S ι χ q hdet htriv hrow) A).trans
    ((profiniteFramedLimitHomEquiv O G n ρ₀ A).subtypeEquiv fun f ↦ by
      rw [universalArithmeticIdeal, kills_framedArithmeticIdeal_iff]
      apply and_congr _ (Iff.rfl)
      apply forall_congr'
      intro g
      have hd := RingHom.map_det f.hom.toRingHom (r g).val
      change f.hom (r g).val.det = _ at hd
      exact iff_of_eq (congrArg (fun x : A ↦ x = algebraMap O A (δ g)) hd))

/-- Forgetting determinant and inertia gives the existing specified local quotient. -/
def universalArithmeticToLocal :
    universalLocalQuotientObject O G n ρ₀ ι χ q hrow ⟶
      universalArithmeticObject O G n ρ₀ δ S ι χ q hdet htriv hrow :=
  factorClosedIdeal U (universalLocalQuotientIdeal O G n ρ₀ ι χ q)
    (universalLocalQuotientIdeal_closed O G n ρ₀ ι χ q)
    (universalLocalQuotientIdeal_ne_top O G n ρ₀ ι χ q hrow)
    (closedIdealQuotientHom U (universalArithmeticIdeal O G n ρ₀ δ S ι χ q)
      (universalArithmeticIdeal_closed O G n ρ₀ δ S ι χ q)
      (universalArithmeticIdeal_ne_top O G n ρ₀ δ S ι χ q hdet htriv hrow)) (by
        intro x hx
        change Ideal.Quotient.mk (universalArithmeticIdeal O G n ρ₀ δ S ι χ q) x = 0
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        exact subset_closure ((le_sup_right : framedQuotientIdeal U ((r).comp ι) χ q ≤
          (framedDeterminantIdeal U r δ ⊔ framedTrivialityIdeal U r S) ⊔
            framedQuotientIdeal U ((r).comp ι) χ q) hx))

omit [TotallyDisconnectedSpace G] in
/-- The map between quotients retains every original universal parameter. -/
@[simp] theorem universalArithmeticToLocal_mk (x : U) :
    (universalArithmeticToLocal O G n ρ₀ δ S ι χ q hdet htriv hrow).hom
      (Ideal.Quotient.mk (universalLocalQuotientIdeal O G n ρ₀ ι χ q) x) =
        Ideal.Quotient.mk (universalArithmeticIdeal O G n ρ₀ δ S ι χ q) x := rfl

omit [TotallyDisconnectedSpace G] in
/-- The arithmetic object is a quotient of the existing local object, not just a mapped ring. -/
theorem universalArithmeticToLocal_surjective :
    Function.Surjective (universalArithmeticToLocal O G n ρ₀ δ S ι χ q hdet htriv hrow).hom := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk (universalLocalQuotientIdeal O G n ρ₀ ι χ q) x, rfl⟩

end Deformation
