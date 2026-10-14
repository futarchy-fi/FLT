/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteModificationSections
public import FLT.Mazur.WeierstrassCoefficientShearSpecialization
public import FLT.Mazur.WeierstrassSmoothFaithfulCoefficientDescent

/-!
# Arithmetic sections in the actual coefficient-sheared closed fiber

Lift the closed restriction of the original integral section through the
proved cartesian square. Any nontrivial residue algebra detects equality,
so changing to tangent coefficients cannot lose arithmetic injectivity.
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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra A S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "qS" => Spec.map (CommRingCat.ofHom (algebraMap A S))
local notation "g" => coefficientShearGluedStructure hπ data S r j hj
local notation "pS" => coefficientShearGluedProjection hπ data S r j hj
local notation "H" => coefficientShearGlued_isPullback hπ data S r j hj

/-- The actual coefficient-model point obtained from the original integral section. -/
def e0CoefficientSection (P : ellipticE0 A W) :
    Spec (.of S) ⟶ coefficientShearGlued hπ data S r j hj :=
  (H).lift (𝟙 _) (qS ≫ e0FiniteSection A hπ data j hj P)
    (by rw [Category.assoc, e0FiniteSection_structure, Category.comp_id, Category.id_comp])

/-- The coefficient section is over its actual coefficient spectrum. -/
@[reassoc] theorem e0CoefficientSection_structure (P : ellipticE0 A W) :
    e0CoefficientSection A hπ data S r j hj P ≫ g = 𝟙 _ :=
  (H).lift_fst _ _ _

/-- Projection remembers the actual original integral section and the coefficient map. -/
@[reassoc] theorem e0CoefficientSection_projection (P : ellipticE0 A W) :
    e0CoefficientSection A hπ data S r j hj P ≫ pS =
      qS ≫ e0FiniteSection A hπ data j hj P :=
  (H).lift_snd _ _ _

variable [Algebra (ResidueField A) S] [IsScalarTower A (ResidueField A) S]
local notation "q" => Spec.map (CommRingCat.ofHom (residue A))
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap (ResidueField A) S))

/-- The coefficient section projects through the actual closed point of the original model. -/
@[reassoc] theorem e0CoefficientSection_closed_projection (P : ellipticE0 A W) :
    e0CoefficientSection A hπ data S r j hj P ≫ pS =
      b ≫ e0FiniteClosedPoint A hπ data j hj P ≫
        pullback.snd q (finiteGlobalStructure hπ data j hj) := by
  rw [e0CoefficientSection_projection, e0FiniteClosedPoint_projection, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq A (ResidueField A) S).trans (by rfl)

variable [Nontrivial S]

/-- Faithful residue coefficients detect precisely the original arithmetic reduction equality. -/
theorem e0CoefficientSection_eq_iff (P Q : ellipticE0 A W) :
    e0CoefficientSection A hπ data S r j hj P =
        e0CoefficientSection A hπ data S r j hj Q ↔
      smoothReductionHom A W P = smoothReductionHom A W Q := by
  have hfaith : (algebraMap (ResidueField A) S).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have hh := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap (ResidueField A) S))).mpr hfaith
  let _ : Flat b := hh.1
  let _ : Surjective b := hh.2
  let _ : Epi b := Flat.epi_of_flat_of_surjective b
  constructor
  · intro h
    apply (e0SmoothSectionEquiv_special_eq_iff A W P Q).mp
    apply (cancel_mono (finiteGlobalSmoothEmbedding hπ data j hj)).mp
    apply (cancel_epi b).mp
    have he := congrArg (· ≫ pS) h
    rw [e0CoefficientSection_closed_projection, e0CoefficientSection_closed_projection,
      e0FiniteClosedPoint_projection, e0FiniteClosedPoint_projection] at he
    simpa only [e0FiniteSection, Category.assoc] using he
  · intro h
    apply (H).hom_ext
    · rw [e0CoefficientSection_structure, e0CoefficientSection_structure]
    · rw [e0CoefficientSection_closed_projection, e0CoefficientSection_closed_projection,
        (e0FiniteClosedPoint_eq_iff A hπ data j hj P Q).mpr h]

variable [IsAdicComplete (maximalIdeal A) A]

/-- Prime-to-residue torsion stays distinct in the whole actual coefficient model. -/
theorem e0CoefficientSection_injOn_torsion
    (p m : ℕ) [CharP (ResidueField A) p] (hm : ¬ p ∣ m) :
    Set.InjOn (e0CoefficientSection A hπ data S r j hj) {P | m • P = 0} := by
  intro P hP Q hQ h
  exact smoothReductionHom_injOn_torsion_of_not_dvd A W p m hm hP hQ
    ((e0CoefficientSection_eq_iff A hπ data S r j hj P Q).mp h)

variable [IsDiscreteValuationRing A]

/-- Residue-prime torsion stays distinct after coefficient extension at small ramification. -/
theorem e0CoefficientSection_injOn_small_ramification
    (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
    (he : RaynaudParameters.order (p : A) < p - 1) :
    Set.InjOn (e0CoefficientSection A hπ data S r j hj) {P | p • P = 0} := by
  intro P hP Q hQ h
  exact smoothReduction_prime_torsion_injective_small_ramification A W p hp0 he P Q hP hQ
    ((e0CoefficientSection_eq_iff A hπ data S r j hj P Q).mp h)

end FLT.Mazur.WeierstrassDividedDepth
