/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicCoefficientComparison

/-! # Coordinate naturality across coefficient algebras

A coefficient algebra map acts on both explicit cubic charts and gives a
global comparison through the cartesian coefficient square. Coordinate
changes commute with this comparison after mapping their coefficients.
The identity restricts to full torsion, nonzero torsion and cyclic parameters.
For reciprocal root covers it identifies the original reciprocal transport
with transport by the inverse distinguished root on the other cover.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (σ : S →ₐ[R] T)

/-- The chart pullback induced by a homomorphism between coefficient algebras. -/
def chartCoefficientHom (b : Bool) :
    Ring (W.map (algebraMap R S)) b →+* Ring (W.map (algebraMap R T)) b :=
  (chartBaseChangeEquiv W T b).toRingHom.comp
    ((Algebra.TensorProduct.map σ (AlgHom.id R (Ring W b))).toRingHom.comp
      (chartBaseChangeEquiv W S b).symm.toRingHom)

/-- The chart comparison applies the algebra map to the coefficient tensor factor. -/
theorem chartCoefficientHom_tmul (b : Bool) (s : S) (x : Ring W b) :
    chartCoefficientHom W σ b (chartBaseChangeEquiv W S b (s ⊗ₜ[R] x)) =
      chartBaseChangeEquiv W T b (σ s ⊗ₜ[R] x) := by
  simp [chartCoefficientHom]

/-- The comparison preserves the chart coordinates. -/
theorem chartCoefficientHom_coord (b : Bool) (i : Fin 2) :
    chartCoefficientHom W σ b (coord (W.map (algebraMap R S)) b i) =
      coord (W.map (algebraMap R T)) b i := by
  rw [← chartBaseChangeEquiv_coord, chartCoefficientHom_tmul, map_one,
    chartBaseChangeEquiv_coord]

/-- The comparison maps scalars through the coefficient homomorphism. -/
theorem chartCoefficientHom_scalar (b : Bool) (s : S) :
    chartCoefficientHom W σ b (algebraMap S (Ring (W.map (algebraMap R S)) b) s) =
      algebraMap T (Ring (W.map (algebraMap R T)) b) (σ s) := by
  have hs : chartBaseChangeEquiv W S b (s ⊗ₜ[R] (1 : Ring W b)) =
      algebraMap S (Ring (W.map (algebraMap R S)) b) s := (chartBaseChangeEquiv W S b).commutes s
  have ht : chartBaseChangeEquiv W T b (σ s ⊗ₜ[R] (1 : Ring W b)) =
      algebraMap T (Ring (W.map (algebraMap R T)) b) (σ s) :=
    (chartBaseChangeEquiv W T b).commutes (σ s)
  rw [← hs, chartCoefficientHom_tmul, ht]

/-- The chart comparison preserves extension from the original chart. -/
theorem chartCoefficientHom_coefficient (b : Bool) :
    (chartCoefficientHom W σ b).comp (chartCoefficientMap W S b) =
      chartCoefficientMap W T b := by
  apply RingHom.ext
  intro x
  change chartCoefficientHom W σ b (chartBaseChangeEquiv W S b (1 ⊗ₜ[R] x)) = _
  rw [chartCoefficientHom_tmul, map_one]
  rfl

/-- An algebra homomorphism induces a morphism over the original base. -/
theorem coefficientCompare_base :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)) =
        Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact σ.commutes x

/-- The actual global comparison of the two coefficient-extended curves. -/
def coefficientCompareMorphism :
    scheme (W.map (algebraMap R T)) ⟶ scheme (W.map (algebraMap R S)) :=
  (coefficientMorphism_isPullback W S).lift (coefficientMorphism W T)
    (toBase (W.map (algebraMap R T)) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
      rw [Category.assoc, coefficientCompare_base, coefficientMorphism_toBase])

/-- Global comparison preserves projection to the original curve. -/
@[reassoc (attr := simp)]
theorem coefficientCompareMorphism_coefficient :
    coefficientCompareMorphism W σ ≫ coefficientMorphism W S = coefficientMorphism W T :=
  (coefficientMorphism_isPullback W S).lift_fst _ _ _

/-- Global comparison lies over the specified coefficient homomorphism. -/
@[reassoc (attr := simp)]
theorem coefficientCompareMorphism_toBase :
    coefficientCompareMorphism W σ ≫ toBase (W.map (algebraMap R S)) =
      toBase (W.map (algebraMap R T)) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  (coefficientMorphism_isPullback W S).lift_snd _ _ _

/-- The explicit chart comparison lies over the coefficient map. -/
theorem chartCoefficientHom_toBase (b : Bool) :
    Spec.map (CommRingCat.ofHom (chartCoefficientHom W σ b)) ≫
      chartToBase (W.map (algebraMap R S)) b =
        chartToBase (W.map (algebraMap R T)) b ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
  dsimp only [chartToBase]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  exact chartCoefficientHom_scalar W σ b x

/-- The explicit chart pullbacks agree with the global comparison. -/
theorem sourceChart_coefficientCompare (b : Bool) :
    sourceChart (W.map (algebraMap R T)) b ≫ coefficientCompareMorphism W σ =
      Spec.map (CommRingCat.ofHom (chartCoefficientHom W σ b)) ≫
        sourceChart (W.map (algebraMap R S)) b := by
  apply (coefficientMorphism_isPullback W S).hom_ext
  · simp only [Category.assoc, coefficientCompareMorphism_coefficient,
      sourceChart_coefficientMorphism]
    rw [← Category.assoc]
    change _ = (Spec.map (CommRingCat.ofHom (chartCoefficientHom W σ b)) ≫
      Spec.map (CommRingCat.ofHom (chartCoefficientMap W S b))) ≫ sourceChart W b
    rw [← Spec.map_comp]
    change _ = Spec.map (CommRingCat.ofHom
      ((chartCoefficientHom W σ b).comp (chartCoefficientMap W S b))) ≫ sourceChart W b
    rw [chartCoefficientHom_coefficient]
    rfl
  · rw [Category.assoc, coefficientCompareMorphism_toBase, ← Category.assoc,
      sourceChart_toBase, Category.assoc, sourceChart_toBase]
    exact (chartCoefficientHom_toBase W σ b).symm

/-- Successive coefficient extension agrees with direct extension from the base. -/
theorem coefficientCompare_curve :
    (W.map (algebraMap R S)).map σ.toRingHom = W.map (algebraMap R T) := by
  rw [WeierstrassCurve.map_map]
  congr 1
  ext x
  exact σ.commutes x

variable (V : WeierstrassCurve R) (C : VariableChange S)
variable (h : C • W.map (algebraMap R S) = V.map (algebraMap R S))

include h in
/-- Mapping the coefficients of a change preserves its target equation. -/
theorem coefficientCompare_variableChange_equation :
    C.map σ.toRingHom • W.map (algebraMap R T) = V.map (algebraMap R T) := by
  conv_lhs => rw [← coefficientCompare_curve W σ]
  rw [map_variableChange, h, coefficientCompare_curve]

/-- Coordinate pullbacks commute with comparison between coefficient algebras. -/
theorem coefficientCompare_variableChange_affine :
    (chartCoefficientHom V σ false).comp
      (variableChangeIdentifiedAffineMap (W.map (algebraMap R S)) (V.map (algebraMap R S))
        C h).toRingHom =
      (variableChangeIdentifiedAffineMap (W.map (algebraMap R T)) (V.map (algebraMap R T))
        (C.map σ.toRingHom) (coefficientCompare_variableChange_equation W σ V C h)).toRingHom.comp
          (chartCoefficientHom W σ false) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro s
    change chartCoefficientHom V σ false
      (variableChangeIdentifiedAffineMap (W.map (algebraMap R S)) (V.map (algebraMap R S))
        C h (algebraMap S _ s)) =
      variableChangeIdentifiedAffineMap (W.map (algebraMap R T)) (V.map (algebraMap R T))
        (C.map σ.toRingHom) (coefficientCompare_variableChange_equation W σ V C h)
          (chartCoefficientHom W σ false (algebraMap S _ s))
    rw [AlgHom.commutes, chartCoefficientHom_scalar, chartCoefficientHom_scalar, AlgHom.commutes]
  · intro i
    change chartCoefficientHom V σ false
      (variableChangeIdentifiedAffineMap (W.map (algebraMap R S)) (V.map (algebraMap R S))
        C h (coord _ false i)) =
      variableChangeIdentifiedAffineMap (W.map (algebraMap R T)) (V.map (algebraMap R T))
        (C.map σ.toRingHom) (coefficientCompare_variableChange_equation W σ V C h)
          (chartCoefficientHom W σ false (coord _ false i))
    rw [variableChangeIdentifiedAffineMap_coord, chartCoefficientHom_coord,
      variableChangeIdentifiedAffineMap_coord]
    fin_cases i <;> simp [VariableChange.map, map_add, map_mul, map_pow,
      chartCoefficientHom_scalar, chartCoefficientHom_coord]

/-- The global comparison has the asserted affine chart pullback. -/
theorem affineChart_coefficientCompare :
    affineChart (W.map (algebraMap R T)) ≫ coefficientCompareMorphism W σ =
      Spec.map (CommRingCat.ofHom (chartCoefficientHom W σ false)) ≫
        affineChart (W.map (algebraMap R S)) :=
  sourceChart_coefficientCompare W σ false

attribute [local irreducible] variableChangeCongrOverIso coefficientCompareMorphism

private theorem compare_spec_comp {A B D : Type u}
    [CommRing A] [CommRing B] [CommRing D] (f : B →+* D) (g : A →+* B) :
    Spec.map (CommRingCat.ofHom (f.comp g)) =
      Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom g) :=
  Spec.map_comp _ _
private theorem compare_spec_square {A B C D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* D) (f' : A →+* C) (g' : C →+* D)
    (h : g.comp f = g'.comp f') :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom g') ≫ Spec.map (CommRingCat.ofHom f') := by
  rw [← compare_spec_comp, ← compare_spec_comp, h]
private theorem compare_square_comp {A B C D E F : Scheme.{u}}
    {i : A ⟶ B} {j : C ⟶ D} {k : E ⟶ F}
    {f : B ⟶ D} {g : D ⟶ F} {f' : A ⟶ C} {g' : C ⟶ E}
    (h₁ : i ≫ f = f' ≫ j) (h₂ : j ≫ g = g' ≫ k) :
    i ≫ (f ≫ g) = (f' ≫ g') ≫ k := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

/-- Coordinate naturality holds on the affine chart. -/
theorem coefficientCompare_variableChange_chart :
    affineChart (V.map (algebraMap R T)) ≫ (coefficientCompareMorphism V σ ≫
      (variableChangeCongrOverIso (W.map (algebraMap R S)) (V.map (algebraMap R S)) C h).hom.left) =
      affineChart (V.map (algebraMap R T)) ≫
        ((variableChangeCongrOverIso (W.map (algebraMap R T)) (V.map (algebraMap R T))
          (C.map σ.toRingHom) (coefficientCompare_variableChange_equation W σ V C h)).hom.left ≫
            coefficientCompareMorphism W σ) := by
  have hl := compare_square_comp (affineChart_coefficientCompare V σ)
    (affineChart_variableChangeCongr (W.map (algebraMap R S)) (V.map (algebraMap R S)) C h)
  have hr := compare_square_comp
    (affineChart_variableChangeCongr (W.map (algebraMap R T)) (V.map (algebraMap R T))
      (C.map σ.toRingHom) (coefficientCompare_variableChange_equation W σ V C h))
    (affineChart_coefficientCompare W σ)
  apply hl.trans
  apply Eq.trans _ hr.symm
  have hs := compare_spec_square _ _ _ _
    (coefficientCompare_variableChange_affine W σ V C h)
  exact congrArg (fun z => z ≫ affineChart (W.map (algebraMap R S))) hs

/-- Coordinate naturality holds on the glued cubic. -/
theorem coefficientCompare_variableChange :
    coefficientCompareMorphism V σ ≫
      (variableChangeCongrOverIso (W.map (algebraMap R S)) (V.map (algebraMap R S)) C h).hom.left =
      (variableChangeCongrOverIso (W.map (algebraMap R T)) (V.map (algebraMap R T))
        (C.map σ.toRingHom) (coefficientCompare_variableChange_equation W σ V C h)).hom.left ≫
          coefficientCompareMorphism W σ := by
  apply affineChart_hom_ext (V.map (algebraMap R T)) (toBase (W.map (algebraMap R S)))
  · rw [Category.assoc, variableChangeCongr_toBase, coefficientCompareMorphism_toBase,
      Category.assoc, coefficientCompareMorphism_toBase, ← Category.assoc,
      variableChangeCongr_toBase]
  · exact coefficientCompare_variableChange_chart W σ V C h

section TorsionComparison
variable [IsNoetherianRing R] [IsDomain R] [IsNoetherianRing S] [IsDomain S]
variable [IsNoetherianRing T] [IsDomain T] [W.IsElliptic]

/-- Comparison of full torsion across a coefficient algebra map. -/
def coefficientTorsionMap (n : ℕ) :
    (torsionModel (W.map (algebraMap R T)) n).left ⟶
      (torsionModel (W.map (algebraMap R S)) n).left :=
  (coefficientTorsion_isPullback W S n).lift (coefficientTorsionMorphism W T n)
    ((torsionModel (W.map (algebraMap R T)) n).hom ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
    (by rw [Category.assoc, coefficientCompare_base, coefficientTorsionMorphism_toBase])

/-- Full torsion comparison preserves the original torsion projection. -/
@[reassoc (attr := simp)]
theorem coefficientTorsionMap_coefficient (n : ℕ) :
    coefficientTorsionMap W σ n ≫ coefficientTorsionMorphism W S n =
      coefficientTorsionMorphism W T n :=
  (coefficientTorsion_isPullback W S n).lift_fst _ _ _

/-- Full torsion comparison lies over the coefficient map. -/
@[reassoc (attr := simp)]
theorem coefficientTorsionMap_toBase (n : ℕ) :
    coefficientTorsionMap W σ n ≫ (torsionModel (W.map (algebraMap R S)) n).hom =
      (torsionModel (W.map (algebraMap R T)) n).hom ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  (coefficientTorsion_isPullback W S n).lift_snd _ _ _

/-- Full torsion comparison agrees with global curve comparison. -/
theorem coefficientTorsionMap_inclusion (n : ℕ) :
    coefficientTorsionMap W σ n ≫ (torsionInclusion (W.map (algebraMap R S)) n).left =
      (torsionInclusion (W.map (algebraMap R T)) n).left ≫ coefficientCompareMorphism W σ := by
  apply (coefficientMorphism_isPullback W S).hom_ext
  · rw [Category.assoc, ← coefficientTorsionMorphism_inclusion, ← Category.assoc,
      coefficientTorsionMap_coefficient, coefficientTorsionMorphism_inclusion,
      Category.assoc, coefficientCompareMorphism_coefficient]
  · have hs : (torsionInclusion (W.map (algebraMap R S)) n).left ≫
        toBase (W.map (algebraMap R S)) = (torsionModel (W.map (algebraMap R S)) n).hom :=
      (torsionInclusion (W.map (algebraMap R S)) n).w
    have ht : (torsionInclusion (W.map (algebraMap R T)) n).left ≫
        toBase (W.map (algebraMap R T)) = (torsionModel (W.map (algebraMap R T)) n).hom :=
      (torsionInclusion (W.map (algebraMap R T)) n).w
    rw [Category.assoc, hs, coefficientTorsionMap_toBase, Category.assoc,
      coefficientCompareMorphism_toBase, ← Category.assoc, ht]

/-- Comparison of nonzero torsion across a coefficient algebra map. -/
def coefficientNonzeroMap (n : ℕ) [NeZero n] :
    (nonzeroTorsionModel (W.map (algebraMap R T)) n).left ⟶
      (nonzeroTorsionModel (W.map (algebraMap R S)) n).left :=
  (coefficientNonzeroTorsion_isPullback W S n).lift (coefficientNonzeroTorsionMorphism W T n)
    ((nonzeroTorsionModel (W.map (algebraMap R T)) n).hom ≫
      Spec.map (CommRingCat.ofHom σ.toRingHom))
    (by
      rw [Category.assoc, coefficientCompare_base]
      exact (coefficientNonzeroTorsion_isPullback W T n).w)

/-- Nonzero torsion comparison preserves its original projection. -/
@[reassoc (attr := simp)]
theorem coefficientNonzeroMap_coefficient (n : ℕ) [NeZero n] :
    coefficientNonzeroMap W σ n ≫ coefficientNonzeroTorsionMorphism W S n =
      coefficientNonzeroTorsionMorphism W T n :=
  (coefficientNonzeroTorsion_isPullback W S n).lift_fst _ _ _

/-- Nonzero torsion comparison lies over the coefficient map. -/
@[reassoc (attr := simp)]
theorem coefficientNonzeroMap_toBase (n : ℕ) [NeZero n] :
    coefficientNonzeroMap W σ n ≫ (nonzeroTorsionModel (W.map (algebraMap R S)) n).hom =
      (nonzeroTorsionModel (W.map (algebraMap R T)) n).hom ≫
        Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  (coefficientNonzeroTorsion_isPullback W S n).lift_snd _ _ _

/-- Nonzero comparison agrees with full torsion comparison. -/
theorem coefficientNonzeroMap_inclusion (n : ℕ) [NeZero n] :
    coefficientNonzeroMap W σ n ≫ (nonzeroTorsionInclusion (W.map (algebraMap R S)) n).left =
      (nonzeroTorsionInclusion (W.map (algebraMap R T)) n).left ≫ coefficientTorsionMap W σ n := by
  apply (coefficientTorsion_isPullback W S n).hom_ext
  · rw [Category.assoc, ← coefficientNonzeroTorsionMorphism_inclusion, ← Category.assoc,
      coefficientNonzeroMap_coefficient, coefficientNonzeroTorsionMorphism_inclusion,
      Category.assoc, coefficientTorsionMap_coefficient]
  · rw [Category.assoc, (nonzeroTorsionInclusion (W.map (algebraMap R S)) n).w,
      coefficientNonzeroMap_toBase, Category.assoc, coefficientTorsionMap_toBase,
      ← Category.assoc, (nonzeroTorsionInclusion (W.map (algebraMap R T)) n).w]

variable (p : ℕ) [Fact p.Prime] [Fact (IsUnit (p : R))]
variable [Fact (IsUnit (p : S))] [Fact (IsUnit (p : T))]

/-- Cyclic comparison agrees with comparison of torsion generators. -/
theorem coefficientCyclicMap_quotient :
    coefficientNonzeroMap W σ p ≫ (scalarQuotientMap (W.map (algebraMap R S)) p).left =
      (scalarQuotientMap (W.map (algebraMap R T)) p).left ≫ coefficientCyclicMap W p σ := by
  apply (coefficientScalarQuotient_isPullback W S p).hom_ext
  · rw [Category.assoc, coefficientScalarQuotientMorphism_generators, ← Category.assoc,
      coefficientNonzeroMap_coefficient, ← coefficientScalarQuotientMorphism_generators,
      Category.assoc, coefficientCyclicMap_coefficient]
  · rw [Category.assoc, (scalarQuotientMap (W.map (algebraMap R S)) p).w,
      coefficientNonzeroMap_toBase, Category.assoc, coefficientCyclicMap_toBase,
      ← Category.assoc, (scalarQuotientMap (W.map (algebraMap R T)) p).w]

variable [V.IsElliptic]
variable (e : groupModel (V.map (algebraMap R S)) ≅ groupModel (W.map (algebraMap R S)))
variable (f : groupModel (V.map (algebraMap R T)) ≅ groupModel (W.map (algebraMap R T)))
variable [IsMonHom e.hom] [IsMonHom e.inv] [IsMonHom f.hom] [IsMonHom f.inv]
variable (he : coefficientCompareMorphism V σ ≫ e.hom.left =
  f.hom.left ≫ coefficientCompareMorphism W σ)

omit [Fact p.Prime] [Fact (IsUnit (p : R))] [Fact (IsUnit (p : S))]
    [Fact (IsUnit (p : T))] in
include he in
/-- Naturality of curve maps restricts to full torsion. -/
theorem coefficientCompare_torsionTransport (n : ℕ) :
    coefficientTorsionMap V σ n ≫ (torsionTransportIso e n).hom.left =
      (torsionTransportIso f n).hom.left ≫ coefficientTorsionMap W σ n := by
  apply (cancel_mono (torsionInclusion (W.map (algebraMap R S)) n).left).mp
  have h₁ := congrArg Over.Hom.left (torsionTransport_inclusion e.hom n)
  have h₂ := congrArg Over.Hom.left (torsionTransport_inclusion f.hom n)
  change (torsionTransportIso e n).hom.left ≫ _ = _ ≫ e.hom.left at h₁
  change (torsionTransportIso f n).hom.left ≫ _ = _ ≫ f.hom.left at h₂
  rw [Category.assoc, h₁, ← Category.assoc, coefficientTorsionMap_inclusion,
    Category.assoc, he, ← Category.assoc, ← h₂, Category.assoc,
    ← coefficientTorsionMap_inclusion, ← Category.assoc]

omit [Fact p.Prime] [Fact (IsUnit (p : R))] [Fact (IsUnit (p : S))]
    [Fact (IsUnit (p : T))] in
include he in
/-- Naturality of curve maps restricts to nonzero torsion. -/
theorem coefficientCompare_nonzeroTransport (n : ℕ) [NeZero n] :
    coefficientNonzeroMap V σ n ≫ (groupNonzeroTorsionTransportIso n e).hom.left =
      (groupNonzeroTorsionTransportIso n f).hom.left ≫ coefficientNonzeroMap W σ n := by
  apply (cancel_mono (nonzeroTorsionInclusion (W.map (algebraMap R S)) n).left).mp
  have h₁ := congrArg Over.Hom.left (groupNonzeroTorsionTransportIso_inclusion n e)
  have h₂ := congrArg Over.Hom.left (groupNonzeroTorsionTransportIso_inclusion n f)
  change _ ≫ _ = _ ≫ _ at h₁ h₂
  rw [Category.assoc, h₁, ← Category.assoc, coefficientNonzeroMap_inclusion,
    Category.assoc, coefficientCompare_torsionTransport W σ V e f he n,
    ← Category.assoc, ← h₂, Category.assoc, ← coefficientNonzeroMap_inclusion,
    ← Category.assoc]

include he in
/-- Naturality of curve maps passes to cyclic parameters. -/
theorem coefficientCompare_cyclicTransport :
    coefficientCyclicMap V p σ ≫ (groupCyclicParameterIso p e).hom.left =
      (groupCyclicParameterIso p f).hom.left ≫ coefficientCyclicMap W p σ := by
  apply (cancel_epi (scalarQuotientMap (V.map (algebraMap R T)) p).left).mp
  have h₁ := congrArg Over.Hom.left (groupCyclicParameterIso_quotient p e)
  have h₂ := congrArg Over.Hom.left (groupCyclicParameterIso_quotient p f)
  change _ ≫ _ = _ ≫ _ at h₁ h₂
  rw [← Category.assoc, ← coefficientCyclicMap_quotient, Category.assoc, ← h₁,
    ← Category.assoc, coefficientCompare_nonzeroTransport W σ V e f he p,
    Category.assoc, coefficientCyclicMap_quotient, ← Category.assoc, h₂, Category.assoc]

/-- Coordinate changes commute with cyclic coefficient comparison. -/
theorem coefficientCompare_variableChange_cyclic :
    coefficientCyclicMap V p σ ≫
      (groupCyclicParameterIso p (variableChangeCongrOverIso
        (W.map (algebraMap R S)) (V.map (algebraMap R S)) C h)).hom.left =
      (groupCyclicParameterIso p (variableChangeCongrOverIso
        (W.map (algebraMap R T)) (V.map (algebraMap R T)) (C.map σ.toRingHom)
          (coefficientCompare_variableChange_equation W σ V C h))).hom.left ≫
            coefficientCyclicMap W p σ :=
  coefficientCompare_cyclicTransport W σ V p _ _
    (coefficientCompare_variableChange W σ V C h)
end TorsionComparison

section ReciprocalChange
variable (d : Rˣ) [Fact (IsUnit (2 : R))]

/-- Reciprocal root comparison maps the coordinate scaling to the inverse root. -/
theorem quadraticReciprocalChange_map :
    (legendreReciprocalChange (quadraticEtaleUnit d)).map (quadraticReciprocalHom d).toRingHom =
      legendreReciprocalChange (quadraticEtaleUnit d⁻¹)⁻¹ := by
  ext <;> simp only [legendreReciprocalChange, VariableChange.map, map_zero,
    Units.coe_map, MonoidHom.coe_ofClass]
  exact congrArg Units.val (quadraticReciprocalHom_unit_map d)

variable (hd : legendreReciprocalChange (quadraticEtaleUnit d) •
  W.map (algebraMap R (QuadraticEtaleRing d)) = V.map (algebraMap R (QuadraticEtaleRing d)))

include hd in
/-- The inverse-root change has the transported target equation. -/
theorem quadraticReciprocalChange_equation :
    legendreReciprocalChange (quadraticEtaleUnit d⁻¹)⁻¹ •
      W.map (algebraMap R (QuadraticEtaleRing d⁻¹)) =
        V.map (algebraMap R (QuadraticEtaleRing d⁻¹)) := by
  rw [← quadraticReciprocalChange_map]
  exact coefficientCompare_variableChange_equation W (quadraticReciprocalHom d) V _ hd

variable [IsNoetherianRing R] [IsDomain R] [W.IsElliptic] [V.IsElliptic]
variable [IsNoetherianRing (QuadraticEtaleRing d)] [IsDomain (QuadraticEtaleRing d)]
variable (p : ℕ) [Fact p.Prime] [Fact (IsUnit (p : R))]
variable [Fact (IsUnit (p : QuadraticEtaleRing d))]
local instance : IsNoetherianRing (QuadraticEtaleRing d⁻¹) :=
  quadraticReciprocal_isNoetherian d
local instance : IsDomain (QuadraticEtaleRing d⁻¹) :=
  quadraticReciprocal_isDomain d
local instance : Fact (IsUnit (p : QuadraticEtaleRing d⁻¹)) :=
  ⟨by simpa only [map_natCast] using
    (Fact.out : IsUnit (p : QuadraticEtaleRing d)).map (quadraticReciprocalHom d)⟩

/-- The reciprocal cyclic isomorphism uses the coefficient comparison map. -/
theorem quadraticReciprocalCyclicIso_hom :
    (quadraticReciprocalCyclicIso W p d).hom =
      coefficientCyclicMap W p (quadraticReciprocalHom d) := rfl

/-- Reciprocal cyclic transport corresponds to inverse-root transport on the other cover. -/
theorem quadraticReciprocalChange_cyclic :
    (quadraticReciprocalCyclicIso V p d).hom ≫
      (groupCyclicParameterIso p (variableChangeCongrOverIso
        (W.map (algebraMap R (QuadraticEtaleRing d)))
        (V.map (algebraMap R (QuadraticEtaleRing d)))
        (legendreReciprocalChange (quadraticEtaleUnit d)) hd)).hom.left =
      (groupCyclicParameterIso p (variableChangeCongrOverIso
        (W.map (algebraMap R (QuadraticEtaleRing d⁻¹)))
        (V.map (algebraMap R (QuadraticEtaleRing d⁻¹)))
        (legendreReciprocalChange (quadraticEtaleUnit d⁻¹)⁻¹)
        (quadraticReciprocalChange_equation W V d hd))).hom.left ≫
          (quadraticReciprocalCyclicIso W p d).hom := by
  rw [quadraticReciprocalCyclicIso_hom, quadraticReciprocalCyclicIso_hom]
  simpa only [quadraticReciprocalChange_map] using
    coefficientCompare_variableChange_cyclic W (quadraticReciprocalHom d) V
      (legendreReciprocalChange (quadraticEtaleUnit d)) hd p
end ReciprocalChange

end WeierstrassCurve.CubicCharts
