/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticPositiveSplitSpecialization
import all FLT.Mazur.WeierstrassDividedPositiveSplitSmoothGroup

/-!
# Original arithmetic torsion subgroups retain their order in the split fiber

These equivalences restrict the actual arithmetic specialization homomorphism.
Injectivity is proved from the original formal reduction kernel, and hence
applies to original generic torsion subgroups, not only to residue points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped MonObj
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
  [IsAdicComplete (maximalIdeal A) A]
local notation "red" => e0PositiveSplitReductionHom A D s hk

/-- A prime-to-residue arithmetic torsion subgroup is isomorphic to its actual specialized image. -/
def e0PositiveSplitTorsionSubgroupEquiv
    (p m : ℕ) [CharP (ResidueField A) p] (hm : ¬ p ∣ m)
    (H : AddSubgroup (ellipticE0 A W)) (hH : ∀ P ∈ H, m • P = 0) :
    H ≃+ H.map red :=
  { Equiv.Set.imageOfInjOn red H (by
      intro P hP Q hQ h
      exact e0PositiveSplitReductionHom_injOn_torsion A hπ data D s hs hstart hk hp
        p m hm (hH P hP) (hH Q hQ) h) with
    map_add' := fun P Q => Subtype.ext (map_add red P.val Q.val) }

/-- The torsion subgroup equivalence is the original arithmetic specialization on each point. -/
theorem e0PositiveSplitTorsionSubgroupEquiv_apply
    (p m : ℕ) [CharP (ResidueField A) p] (hm : ¬ p ∣ m)
    (H : AddSubgroup (ellipticE0 A W)) (hH : ∀ P ∈ H, m • P = 0) (P : H) :
    (e0PositiveSplitTorsionSubgroupEquiv A hπ data D s hs hstart hk hp p m hm H hH P).val =
      red P.val := rfl

include hπ data hs hstart hp in
/-- In particular every finite prime-to-residue subgroup retains its exact original order. -/
theorem e0PositiveSplitTorsionSubgroup_card
    (p m : ℕ) [CharP (ResidueField A) p] (hm : ¬ p ∣ m)
    (H : AddSubgroup (ellipticE0 A W)) (hH : ∀ P ∈ H, m • P = 0) :
    Nat.card (H.map red) = Nat.card H :=
  Nat.card_congr
    (e0PositiveSplitTorsionSubgroupEquiv A hπ data D s hs hstart hk hp p m hm H hH).toEquiv.symm

variable [IsDiscreteValuationRing A]

/-- A residue-prime subgroup is its actual specialized image at small ramification. -/
def e0PositiveSplitSmallRamificationSubgroupEquiv
    (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
    (he : RaynaudParameters.order (p : A) < p - 1)
    (H : AddSubgroup (ellipticE0 A W)) (hH : ∀ P ∈ H, p • P = 0) :
    H ≃+ H.map red :=
  { Equiv.Set.imageOfInjOn red H (by
      intro P hP Q hQ h
      exact e0PositiveSplitReductionHom_injOn_small_ramification
        A hπ data D s hs hstart hk hp p hp0 he (hH P hP) (hH Q hQ) h) with
    map_add' := fun P Q => Subtype.ext (map_add red P.val Q.val) }

/-- The residue-prime equivalence also keeps each original arithmetic section. -/
theorem e0PositiveSplitSmallRamificationSubgroupEquiv_apply
    (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
    (he : RaynaudParameters.order (p : A) < p - 1)
    (H : AddSubgroup (ellipticE0 A W)) (hH : ∀ P ∈ H, p • P = 0) (P : H) :
    (e0PositiveSplitSmallRamificationSubgroupEquiv
      A hπ data D s hs hstart hk hp p hp0 he H hH P).val = red P.val := rfl

include hπ data hs hstart hp in
/-- The actual split fiber retains the exact order of every small-ramification p-subgroup. -/
theorem e0PositiveSplitSmallRamificationSubgroup_card
    (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
    (he : RaynaudParameters.order (p : A) < p - 1)
    (H : AddSubgroup (ellipticE0 A W)) (hH : ∀ P ∈ H, p • P = 0) :
    Nat.card (H.map red) = Nat.card H :=
  Nat.card_congr (e0PositiveSplitSmallRamificationSubgroupEquiv
    A hπ data D s hs hstart hk hp p hp0 he H hH).toEquiv.symm

end FLT.Mazur.WeierstrassDividedDepth
