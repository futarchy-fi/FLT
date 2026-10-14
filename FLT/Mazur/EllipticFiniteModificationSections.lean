/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSmoothSectionSpecialization
public import FLT.Mazur.WeierstrassDividedGlobalFiniteSmoothEmbedding
public import FLT.Mazur.WeierstrassDividedGlobalTensorEmbedding

/-!
# Arithmetic sections on the actual finite modifications

Every original E₀ point gives an integral section at every finite depth.
Its closed restriction is a point of the actual fiber product. Equality of
these closed points is precisely equality under arithmetic smooth reduction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "q" => Spec.map (CommRingCat.ofHom (residue A))
local notation "f" => finiteGlobalStructure hπ data j hj

/-- The original arithmetic section lifted through the complete original smooth embedding. -/
def e0FiniteSection (P : ellipticE0 A W) :
    Spec (.of A) ⟶ finiteGlobalModel hπ data j hj :=
  (e0SmoothSectionEquiv A W P).left ≫ finiteGlobalSmoothEmbedding hπ data j hj

/-- The lifted morphism is an actual section over the original valuation ring. -/
@[reassoc] theorem e0FiniteSection_structure (P : ellipticE0 A W) :
    e0FiniteSection A hπ data j hj P ≫ f = 𝟙 _ := by
  rw [e0FiniteSection, Category.assoc, finiteGlobalSmoothEmbedding_structure]
  exact (e0SmoothSectionEquiv A W P).w

/-- Contraction recovers the original integral section, not just its generic point. -/
@[reassoc] theorem e0FiniteSection_contraction (P : ellipticE0 A W) :
    e0FiniteSection A hπ data j hj P ≫ finiteGlobalContraction hπ data j hj =
      integralPointSection A W P.val := by
  rw [e0FiniteSection, Category.assoc, finiteGlobalSmoothEmbedding_contraction]
  exact smoothIntegralPointSection_inclusion A W P.val P.property

/-- Every modification step retains the same original integral section. -/
@[reassoc] theorem e0FiniteSection_step (hnext : j + 1 ≤ n) (P : ellipticE0 A W) :
    e0FiniteSection A hπ data (j + 1) hnext P ≫ finiteGlobalStep hπ data j hnext =
      e0FiniteSection A hπ data j (Nat.le_of_succ_le hnext) P := by
  rw [e0FiniteSection, Category.assoc, finiteGlobalSmoothEmbedding_step]
  rfl

/-- The genuine closed-fiber point obtained by restricting the integral section. -/
def e0FiniteClosedPoint (P : ellipticE0 A W) :
    Spec (.of (ResidueField A)) ⟶ finiteGlobalTensorModel hπ data (ResidueField A) j hj :=
  pullback.lift (𝟙 _) (q ≫ e0FiniteSection A hπ data j hj P)
    (by rw [Category.assoc, e0FiniteSection_structure, Category.comp_id, Category.id_comp]; rfl)

/-- The closed point is rational over the actual residue field. -/
@[reassoc] theorem e0FiniteClosedPoint_structure (P : ellipticE0 A W) :
    e0FiniteClosedPoint A hπ data j hj P ≫ pullback.fst q f = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- Its original-model projection is the closed restriction of the actual integral section. -/
@[reassoc] theorem e0FiniteClosedPoint_projection (P : ellipticE0 A W) :
    e0FiniteClosedPoint A hπ data j hj P ≫ pullback.snd q f =
      q ≫ e0FiniteSection A hπ data j hj P :=
  pullback.lift_snd _ _ _

/-- Closed points of these sections agree exactly when their arithmetic reductions agree. -/
theorem e0FiniteClosedPoint_eq_iff (P Q : ellipticE0 A W) :
    e0FiniteClosedPoint A hπ data j hj P = e0FiniteClosedPoint A hπ data j hj Q ↔
      smoothReductionHom A W P = smoothReductionHom A W Q := by
  constructor
  · intro h
    apply (e0SmoothSectionEquiv_special_eq_iff A W P Q).mp
    apply (cancel_mono (finiteGlobalSmoothEmbedding hπ data j hj)).mp
    have hp := congrArg (· ≫ pullback.snd q f) h
    simpa only [e0FiniteClosedPoint_projection, e0FiniteSection, Category.assoc] using hp
  · intro h
    apply (IsPullback.of_hasPullback q f).hom_ext
    · rw [e0FiniteClosedPoint_structure, e0FiniteClosedPoint_structure]
    · rw [e0FiniteClosedPoint_projection, e0FiniteClosedPoint_projection, e0FiniteSection,
        e0FiniteSection, ← Category.assoc, ← Category.assoc,
        (e0SmoothSectionEquiv_special_eq_iff A W P Q).mpr h]

variable [IsAdicComplete (maximalIdeal A) A]

/-- Arithmetic prime-to-residue torsion remains distinct in every actual modified closed fiber. -/
theorem e0FiniteClosedPoint_injOn_torsion
    (p m : ℕ) [CharP (ResidueField A) p] (hm : ¬ p ∣ m) :
    Set.InjOn (e0FiniteClosedPoint A hπ data j hj) {P | m • P = 0} := by
  intro P hP Q hQ h
  exact smoothReductionHom_injOn_torsion_of_not_dvd A W p m hm hP hQ
    ((e0FiniteClosedPoint_eq_iff A hπ data j hj P Q).mp h)

variable [IsDiscreteValuationRing A]

/-- At small ramification the actual modified closed fiber also distinguishes p-torsion. -/
theorem e0FiniteClosedPoint_injOn_small_ramification
    (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
    (he : RaynaudParameters.order (p : A) < p - 1) :
    Set.InjOn (e0FiniteClosedPoint A hπ data j hj) {P | p • P = 0} := by
  intro P hP Q hQ h
  exact smoothReduction_prime_torsion_injective_small_ramification A W p hp0 he P Q hP hQ
    ((e0FiniteClosedPoint_eq_iff A hπ data j hj P Q).mp h)

end FLT.Mazur.WeierstrassDividedDepth
