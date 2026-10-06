/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicClassicalReduction
public import FLT.EllipticCurve.SmallResidueTorsion

/-! # Coordinate compatibility and the prime-to-residue-characteristic reduction kernel -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open MonoidalCategory CartesianMonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- An integral affine solution defines an actual section of the cubic. -/
def affineSection (x y : R) (h : W.toAffine.Equation x y) :
    𝟙_ (Over (Spec (.of R))) ⟶ groupModel W :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom
      (affineEvaluation W x y (by simpa using h)).toRingHom) ≫ affineChart W) (by
        change (Spec.map (CommRingCat.ofHom
          (affineEvaluation W x y (by simpa using h)).toRingHom) ≫ affineChart W) ≫
            toBase W = 𝟙 _
        rw [Category.assoc, affineChart_toBase]
        change Spec.map (CommRingCat.ofHom
          (affineEvaluation W x y (by simpa using h)).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R (Ring W false))) = 𝟙 _
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
        apply CommRingCat.hom_ext
        exact (affineEvaluation W x y (by simpa using h)).comp_algebraMap)

theorem affineEvaluation_baseChange (x y : R) (h : W.toAffine.Equation x y)
    {S : Type u} [CommRing S] [Algebra R S] :
    (Algebra.ofId R S).comp (affineEvaluation W x y (by simpa using h)) =
      affineEvaluation W (algebraMap R S x) (algebraMap R S y)
        (Affine.Equation.map (algebraMap R S) h) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change algebraMap R S (affineEvaluation W x y (by simpa using h) (coord W false i)) =
    affineEvaluation W (algebraMap R S x) (algebraMap R S y)
      (Affine.Equation.map (algebraMap R S) h) (coord W false i)
  fin_cases i <;> simp

theorem affineSection_restrict [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]
    (K : Type u) [Field K] [Algebra R K] [DecidableEq K]
    (x y : R) (h : W.toAffine.Equation x y) :
    sectionRestriction W K (affineSection W x y h) =
      classicalPointHom W K (Multiplicative.ofAdd
        (Affine.Point.some (algebraMap R K x) (algebraMap R K y)
          (Affine.equation_iff_nonsingular.mp (Affine.Equation.map (algebraMap R K) h)))) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
      (Spec.map (CommRingCat.ofHom
        (affineEvaluation W x y (by simpa using h)).toRingHom) ≫ affineChart W) =
    Spec.map (CommRingCat.ofHom
      (affineEvaluation W (algebraMap R K x) (algebraMap R K y)
        (Affine.Equation.map (algebraMap R K) h)).toRingHom) ≫ affineChart W
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (affineEvaluation_baseChange W x y h)

/-- On integral affine points the properness-based reduction is ordinary coordinate reduction. -/
theorem classicalReductionHom_affine [IsDomain R] [ValuationRing R]
    [IsNoetherianRing R] [W.IsElliptic]
    (K k : Type u) [Field K] [Algebra R K] [IsFractionRing R K] [DecidableEq K]
    [Field k] [Algebra R k] [DecidableEq k]
    (x y : R) (h : W.toAffine.Equation x y) :
    classicalReductionHom W K k
        (Affine.Point.some (algebraMap R K x) (algebraMap R K y)
          (Affine.equation_iff_nonsingular.mp (Affine.Equation.map (algebraMap R K) h))) =
      Affine.Point.some (algebraMap R k x) (algebraMap R k y)
        (Affine.equation_iff_nonsingular.mp (Affine.Equation.map (algebraMap R k) h)) := by
  change Multiplicative.ofAdd (classicalReductionHom W K k _) = Multiplicative.ofAdd _
  apply (classicalPointEquiv W k).injective
  change (classicalPointEquiv W k)
      ((classicalPointEquiv W k).symm
        (specializationHom W K k (classicalPointHom W K (Multiplicative.ofAdd _)))) =
    classicalPointHom W k (Multiplicative.ofAdd _)
  rw [MulEquiv.apply_symm_apply, ← affineSection_restrict W K x y h,
    specializationHom_section, affineSection_restrict]

/-- The properness-based reduction has no nonzero torsion in its kernel when the
order is invertible in the valuation ring. The integrality step is the proved
division-polynomial argument, not a formal-group assumption. -/
theorem classicalReductionHom_kernel_torsion
    {K : Type u} [Field K] [DecidableEq K]
    (A : ValuationSubring K) [IsNoetherianRing A] (E : WeierstrassCurve A) [E.IsElliptic]
    [DecidableEq (IsLocalRing.ResidueField A)]
    {n : ℕ} (hn : IsUnit (n : A))
    {P : (E.map (algebraMap A K)).toAffine.Point}
    (ht : n • P = 0)
    (hr : classicalReductionHom E K (IsLocalRing.ResidueField A) P = 0) : P = 0 := by
  cases P with
  | zero => rfl
  | some x y hP =>
    obtain ⟨hx, hy⟩ := E.integral_coordinates_of_unit_nsmul A hn hP ht
    let a : A := ⟨x, hx⟩
    let b : A := ⟨y, hy⟩
    have he : E.toAffine.Equation a b := by
      exact (Affine.map_equation E.toAffine (f := algebraMap A K)
        (IsFractionRing.injective A K) a b).mp hP.1
    have hh := classicalReductionHom_affine E K (IsLocalRing.ResidueField A) a b he
    have hz : Affine.Point.some _ _
        (Affine.equation_iff_nonsingular.mp
          (Affine.Equation.map (algebraMap A (IsLocalRing.ResidueField A)) he)) = 0 := by
      exact hh.symm.trans hr
    cases hz

/-- Reduction is injective on points killed by an integer invertible in the valuation ring. -/
theorem classicalReductionHom_torsion_injective
    {K : Type u} [Field K] [DecidableEq K]
    (A : ValuationSubring K) [IsNoetherianRing A] (E : WeierstrassCurve A) [E.IsElliptic]
    [DecidableEq (IsLocalRing.ResidueField A)]
    {n : ℕ} (hn : IsUnit (n : A))
    {P Q : (E.map (algebraMap A K)).toAffine.Point}
    (hP : n • P = 0) (hQ : n • Q = 0)
    (hred : classicalReductionHom E K (IsLocalRing.ResidueField A) P =
      classicalReductionHom E K (IsLocalRing.ResidueField A) Q) : P = Q := by
  apply sub_eq_zero.mp
  apply classicalReductionHom_kernel_torsion A E hn
  · simp only [nsmul_sub, hP, hQ, sub_self]
  · rw [map_sub, hred, sub_self]

/-- Specialization is injective on invertible-order torsion in the actual
group of generic-fiber scheme points. -/
theorem specializationHom_torsion_injective
    {K : Type u} [Field K]
    (A : ValuationSubring K) [IsNoetherianRing A] (E : WeierstrassCurve A) [E.IsElliptic]
    {n : ℕ} (hn : IsUnit (n : A))
    {P Q : pointSource (R := A) K ⟶ groupModel E}
    (hP : P ^ n = 1) (hQ : Q ^ n = 1)
    (hred : specializationHom E K (IsLocalRing.ResidueField A) P =
      specializationHom E K (IsLocalRing.ResidueField A) Q) : P = Q := by
  classical
  let e := classicalPointEquiv E K
  apply e.symm.injective
  change (e.symm P).toAdd = (e.symm Q).toAdd
  apply classicalReductionHom_torsion_injective A E hn
  · change e.symm P ^ n = 1
    rw [← map_pow, hP, map_one]
  · change e.symm Q ^ n = 1
    rw [← map_pow, hQ, map_one]
  · change ((classicalPointEquiv E (IsLocalRing.ResidueField A)).symm
        (specializationHom E K (IsLocalRing.ResidueField A) (e (e.symm P)))).toAdd =
      ((classicalPointEquiv E (IsLocalRing.ResidueField A)).symm
        (specializationHom E K (IsLocalRing.ResidueField A) (e (e.symm Q)))).toAdd
    rw [e.apply_symm_apply, e.apply_symm_apply, hred]

/-- Two invertible-order torsion sections agreeing on the special fiber are equal. -/
theorem torsion_sections_eq_of_specialFiber_eq
    {K : Type u} [Field K]
    (A : ValuationSubring K) [IsNoetherianRing A] (E : WeierstrassCurve A) [E.IsElliptic]
    {n : ℕ} (hn : IsUnit (n : A))
    {s t : 𝟙_ (Over (Spec (.of A))) ⟶ groupModel E}
    (hs : s ^ n = 1) (ht : t ^ n = 1)
    (hred : sectionRestriction E (IsLocalRing.ResidueField A) s =
      sectionRestriction E (IsLocalRing.ResidueField A) t) : s = t := by
  classical
  apply genericRestriction_injective E (K := K)
  change sectionRestriction E K s = sectionRestriction E K t
  apply specializationHom_torsion_injective A E hn
  · rw [← map_pow, hs, map_one]
  · rw [← map_pow, ht, map_one]
  · simpa only [specializationHom_section] using hred

/-- The order of a point killed by an invertible integer is preserved exactly
under good reduction. -/
theorem classicalReductionHom_addOrderOf
    {K : Type u} [Field K] [DecidableEq K]
    (A : ValuationSubring K) [IsNoetherianRing A] (E : WeierstrassCurve A) [E.IsElliptic]
    [DecidableEq (IsLocalRing.ResidueField A)]
    {n : ℕ} (hn : IsUnit (n : A))
    {P : (E.map (algebraMap A K)).toAffine.Point} (ht : n • P = 0) :
    addOrderOf (classicalReductionHom E K (IsLocalRing.ResidueField A) P) =
      addOrderOf P := by
  apply addOrderOf_eq_addOrderOf_iff.mpr
  intro m
  constructor
  · intro hm
    apply classicalReductionHom_kernel_torsion A E hn
    · rw [smul_comm n m, ht, smul_zero]
    · rw [map_nsmul]
      exact hm
  · intro hm
    rw [← map_nsmul, hm, map_zero]

end WeierstrassCurve.CubicCharts
