/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticCoefficientSmoothSectionGroup
public import FLT.Mazur.WeierstrassDividedPositiveSplitIdentitySubgroup

/-!
# Arithmetic specialization into the actual strict positive split group

Specialize original E₀ sections and apply the original smooth identity
inclusion. The resulting homomorphism projects to the genuine closed point
of the integral modification, and is injective on the indicated torsion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing MonoidalCategory MonObj
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "k" => ResidueField A
local notation "V" => W.map (algebraMap A k)
local notation "T" => Over.mk (𝟙 (Spec (.of k)))
local notation "G" => PolygonSplitGroup.model k (2 * s + 5)
local notation "g" => (positiveSplitOriginalSmoothGroupHom D s hk).hom.hom.hom
local notation "M" => positiveSplitCycleSmoothMap hπ data D s hs hstart hk hp

/-- Arithmetic specialization to the original split smooth group with its existing group law. -/
def e0PositiveSplitReductionHom : ellipticE0 A W →+ Additive ((T) ⟶ G) :=
  let post : ((T) ⟶ (integralSmoothGroup V).X) →* ((T) ⟶ G) :=
    { toFun P := P ≫ g
      map_one' := MonObj.one_comp g
      map_mul' P Q := MonObj.mul_comp P Q g }
  post.toAdditive.comp (e0SmoothCoefficientSectionHom A W k)

/-- The homomorphism is the actual closed restriction of the original modified integral section. -/
@[reassoc] theorem e0PositiveSplitReductionHom_inclusion (P : ellipticE0 A W) :
    (e0PositiveSplitReductionHom A D s hk P).toMul.left ≫ (M).left =
      e0FiniteClosedPoint A hπ data (s + 1) hs P := by
  change (e0SmoothCoefficientSection A W k P ≫ (g).left) ≫ (M).left = _
  rw [Category.assoc, positiveSplitOriginalSmoothGroupHom_inclusion,
    e0SmoothCoefficientSection_positiveSplit]

include hπ data hs hstart hp in
/-- Equality of specialized group points implies equality of original arithmetic reductions. -/
theorem e0PositiveSplitReductionHom_eq_imp (P Q : ellipticE0 A W)
    (h : e0PositiveSplitReductionHom A D s hk P = e0PositiveSplitReductionHom A D s hk Q) :
    smoothReductionHom A W P = smoothReductionHom A W Q := by
  apply (e0FiniteClosedPoint_eq_iff A hπ data (s + 1) hs P Q).mp
  have he := congrArg (fun a => a.toMul.left ≫ (M).left) h
  simpa only [e0PositiveSplitReductionHom_inclusion] using he

variable [IsAdicComplete (maximalIdeal A) A]

include hπ data hs hstart hp in
/-- Prime-to-residue torsion of the original arithmetic subgroup specializes injectively. -/
theorem e0PositiveSplitReductionHom_injOn_torsion
    (p m : ℕ) [CharP (ResidueField A) p] (hm : ¬ p ∣ m) :
    Set.InjOn (e0PositiveSplitReductionHom A D s hk) {P | m • P = 0} := by
  intro P hP Q hQ h
  exact smoothReductionHom_injOn_torsion_of_not_dvd A W p m hm hP hQ
    (e0PositiveSplitReductionHom_eq_imp A hπ data D s hs hstart hk hp P Q h)

variable [IsDiscreteValuationRing A]

include hπ data hs hstart hp in
/-- Residue-prime arithmetic torsion also specializes injectively below the ramification bound. -/
theorem e0PositiveSplitReductionHom_injOn_small_ramification
    (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
    (he : RaynaudParameters.order (p : A) < p - 1) :
    Set.InjOn (e0PositiveSplitReductionHom A D s hk) {P | p • P = 0} := by
  intro P hP Q hQ h
  exact smoothReduction_prime_torsion_injective_small_ramification A W p hp0 he P Q hP hQ
    (e0PositiveSplitReductionHom_eq_imp A hπ data D s hs hstart hk hp P Q h)

end FLT.Mazur.WeierstrassDividedDepth
