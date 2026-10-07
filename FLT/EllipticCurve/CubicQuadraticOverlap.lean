/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicQuadraticEtale
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # The sign relation on a quadratic covering

The fiber product of a square-root cover with itself is covered by
two disjoint principal opens. Its two roots agree on one open and are
opposites on the other. The actual kernel-pair projections therefore
agree or differ by the explicitly constructed sign involution.
No reducedness or domain assumption is needed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Polynomial
open scoped TensorProduct
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]

/-- Equal squares give the product relation. -/
theorem quadraticRoots_product (u v : R) (h : u ^ 2 = v ^ 2) :
    (u - v) * (u + v) = 0 := by
  linear_combination h

/-- Equal squares give equal roots when their sum is invertible. -/
theorem quadraticRoots_equal (u v : R) (h : u ^ 2 = v ^ 2) (hs : IsUnit (u + v)) :
    u = v := by
  rcases hs with ⟨a, ha⟩
  have hz : (u - v) * (a : R) = 0 := by
    rw [ha]
    exact quadraticRoots_product u v h
  have hh := congrArg (fun x : R => x * (a⁻¹ : Rˣ)) hz
  have : u - v = 0 := by simpa [mul_assoc] using hh
  exact sub_eq_zero.mp this

/-- Equal squares give opposite roots when their difference is invertible. -/
theorem quadraticRoots_opposite (u v : R) (h : u ^ 2 = v ^ 2)
    (hs : IsUnit (u - v)) : u = -v := by
  exact quadraticRoots_equal u (-v) (by simpa only [neg_sq] using h)
    (by simpa only [sub_eq_add_neg] using hs)

/-- The difference and sum that distinguish the two signs. -/
def quadraticSignDenominator (u v : R) : Bool → R
  | false => u - v
  | true => u + v

/-- The sign denominators generate the unit ideal when two and one root are units. -/
theorem quadraticSignDenominators_span (u v : R) (hu : IsUnit u) (h2 : IsUnit (2 : R)) :
    Ideal.span (Set.range (quadraticSignDenominator u v)) = ⊤ := by
  let I := Ideal.span (Set.range (quadraticSignDenominator u v))
  have hm : u - v ∈ I := Ideal.subset_span ⟨false, rfl⟩
  have hp : u + v ∈ I := Ideal.subset_span ⟨true, rfl⟩
  have hh : 2 * u ∈ I := by
    convert I.add_mem hm hp using 1
    ring
  exact I.eq_top_of_isUnit_mem hh (h2.mul hu)

/-- The principal open for one sign. -/
def quadraticSignChart (u v : R) (i : Bool) : Scheme :=
  Spec (.of (Localization.Away (quadraticSignDenominator u v i)))

/-- The localization map for a sign chart. -/
def quadraticSignInclusion (u v : R) (i : Bool) :
    quadraticSignChart u v i ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R
    (Localization.Away (quadraticSignDenominator u v i))))

instance quadraticSignInclusion_open (u v : R) (i : Bool) :
    IsOpenImmersion (quadraticSignInclusion u v i) :=
  IsOpenImmersion.of_isLocalization (quadraticSignDenominator u v i)

/-- The sum and difference charts cover the coefficient spectrum. -/
def quadraticSignCover (u v : R) (hu : IsUnit u) (h2 : IsUnit (2 : R)) :
    (Spec (.of R)).OpenCover where
  I₀ := Bool
  X := quadraticSignChart u v
  f := quadraticSignInclusion u v
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    have hi : ∃ i, quadraticSignDenominator u v i ∉ x.asIdeal := by
      by_contra h
      push Not at h
      apply x.isPrime.ne_top
      apply top_unique
      rw [← quadraticSignDenominators_span u v hu h2]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact h i
    obtain ⟨i, hi⟩ := hi
    have hr := PrimeSpectrum.localization_away_comap_range
      (Localization.Away (quadraticSignDenominator u v i)) (quadraticSignDenominator u v i)
    obtain ⟨y, hy⟩ := (Set.ext_iff.mp hr x).mpr hi
    exact ⟨i, y, hy⟩

/-- The roots coincide on the sum chart. -/
theorem quadraticSignChart_equal (u v : R) (h : u ^ 2 = v ^ 2) :
    algebraMap R (Localization.Away (quadraticSignDenominator u v true)) u =
      algebraMap R (Localization.Away (quadraticSignDenominator u v true)) v := by
  apply quadraticRoots_equal
  · simpa only [map_pow] using congrArg
      (algebraMap R (Localization.Away (quadraticSignDenominator u v true))) h
  · change IsUnit ((algebraMap R (Localization.Away (u + v))) u +
      (algebraMap R (Localization.Away (u + v))) v)
    rw [← map_add]
    exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (u + v)) (u + v)

/-- The roots are opposite on the difference chart. -/
theorem quadraticSignChart_opposite (u v : R) (h : u ^ 2 = v ^ 2) :
    algebraMap R (Localization.Away (quadraticSignDenominator u v false)) u =
      -algebraMap R (Localization.Away (quadraticSignDenominator u v false)) v := by
  apply quadraticRoots_opposite
  · simpa only [map_pow] using congrArg
      (algebraMap R (Localization.Away (quadraticSignDenominator u v false))) h
  · change IsUnit ((algebraMap R (Localization.Away (u - v))) u -
      (algebraMap R (Localization.Away (u - v))) v)
    rw [← map_sub]
    exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (u - v)) (u - v)

/-- The negative distinguished root also satisfies the standard étale presentation. -/
theorem quadraticEtale_neg_hasMap (d : Rˣ) :
    (quadraticEtalePair d).HasMap (-(quadraticEtalePair d).X) := by
  constructor
  · change aeval (-(quadraticEtalePair d).X) (X ^ 2 - C (d : R)) = 0
    rw [map_sub, map_pow, aeval_X, aeval_C, neg_sq]
    have hh := (quadraticEtalePair d).hasMap_X.1
    change aeval (quadraticEtalePair d).X (X ^ 2 - C (d : R)) = 0 at hh
    simpa only [map_sub, map_pow, aeval_X, aeval_C] using hh
  · have hd : (quadraticRootPolynomial d).derivative = 2 * X := by
      simp [quadraticRootPolynomial]
      ring
    have hh := (quadraticEtalePair d).hasMap_X.2
    change IsUnit (aeval (quadraticEtalePair d).X (quadraticRootPolynomial d).derivative) at hh
    change IsUnit (aeval (-(quadraticEtalePair d).X) (quadraticRootPolynomial d).derivative)
    rw [hd, map_mul, map_ofNat, aeval_X] at hh ⊢
    simpa only [mul_neg] using hh.neg

/-- The algebra endomorphism negating the distinguished square root. -/
def quadraticEtaleNeg (d : Rˣ) : QuadraticEtaleRing d →ₐ[R] QuadraticEtaleRing d :=
  (quadraticEtalePair d).lift (-(quadraticEtalePair d).X) (quadraticEtale_neg_hasMap d)

/-- The sign endomorphism negates the root. -/
theorem quadraticEtaleNeg_root (d : Rˣ) :
    quadraticEtaleNeg d (quadraticEtalePair d).X = -(quadraticEtalePair d).X :=
  StandardEtalePair.lift_X _ _ _

/-- The sign endomorphism is an involution. -/
theorem quadraticEtaleNeg_comp_self (d : Rˣ) :
    (quadraticEtaleNeg d).comp (quadraticEtaleNeg d) = AlgHom.id R (QuadraticEtaleRing d) := by
  apply (quadraticEtalePair d).hom_ext
  simp only [AlgHom.comp_apply, AlgHom.id_apply, quadraticEtaleNeg_root, map_neg, neg_neg]

/-- The sign involution as an algebra automorphism. -/
def quadraticEtaleNegEquiv (d : Rˣ) :
    QuadraticEtaleRing d ≃ₐ[R] QuadraticEtaleRing d :=
  AlgEquiv.ofAlgHom (quadraticEtaleNeg d) (quadraticEtaleNeg d)
    (quadraticEtaleNeg_comp_self d) (quadraticEtaleNeg_comp_self d)

/-- The sign endomorphism negates the distinguished root unit. -/
theorem quadraticEtaleNeg_unit (d : Rˣ) :
    quadraticEtaleNeg d (quadraticEtaleUnit d : QuadraticEtaleRing d) =
      -(quadraticEtaleUnit d : QuadraticEtaleRing d) := by
  simpa only [quadraticEtaleUnit, IsUnit.unit_spec] using quadraticEtaleNeg_root d


/-- The coordinate ring of the actual quadratic kernel pair. -/
abbrev QuadraticOverlapRing (d : Rˣ) := QuadraticEtaleRing d ⊗[R] QuadraticEtaleRing d

/-- The root pulled back from the first covering factor. -/
def quadraticOverlapLeftRoot (d : Rˣ) : (QuadraticOverlapRing d)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft :
    QuadraticEtaleRing d →ₐ[R] QuadraticOverlapRing d).toMonoidHom (quadraticEtaleUnit d)

/-- The root pulled back from the second covering factor. -/
def quadraticOverlapRightRoot (d : Rˣ) : (QuadraticOverlapRing d)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight :
    QuadraticEtaleRing d →ₐ[R] QuadraticOverlapRing d).toMonoidHom (quadraticEtaleUnit d)

/-- The two roots in the fiber product have the same square. -/
theorem quadraticOverlapRoots_square (d : Rˣ) :
    (quadraticOverlapLeftRoot d : QuadraticOverlapRing d) ^ 2 =
      (quadraticOverlapRightRoot d : QuadraticOverlapRing d) ^ 2 := by
  change (Algebra.TensorProduct.includeLeft :
    QuadraticEtaleRing d →ₐ[R] QuadraticOverlapRing d)
      (quadraticEtaleUnit d : QuadraticEtaleRing d) ^ 2 =
    (Algebra.TensorProduct.includeRight :
    QuadraticEtaleRing d →ₐ[R] QuadraticOverlapRing d)
      (quadraticEtaleUnit d : QuadraticEtaleRing d) ^ 2
  rw [← map_pow, ← map_pow, quadraticEtaleUnit_square]
  simp only [AlgHom.commutes]


open CategoryTheory.Limits

/-- The tensor-product presentation of the quadratic kernel pair. -/
def quadraticOverlapIso (d : Rˣ) :
    pullback (quadraticEtaleCover d) (quadraticEtaleCover d) ≅
      Spec (.of (QuadraticOverlapRing d)) :=
  pullbackSpecIso R (QuadraticEtaleRing d) (QuadraticEtaleRing d)

/-- The two sign charts cover the actual kernel-pair scheme. -/
def quadraticOverlapCover (d : Rˣ) (h2 : IsUnit (2 : R)) :
    (pullback (quadraticEtaleCover d) (quadraticEtaleCover d)).OpenCover :=
  (quadraticSignCover (quadraticOverlapLeftRoot d : QuadraticOverlapRing d)
    (quadraticOverlapRightRoot d : QuadraticOverlapRing d) (quadraticOverlapLeftRoot d).isUnit
    (by simpa only [map_ofNat] using h2.map (algebraMap R (QuadraticOverlapRing d)))).pushforwardIso
      (quadraticOverlapIso d).inv


/-- The localized coordinate ring of a sign chart in the kernel pair. -/
abbrev QuadraticOverlapChartRing (d : Rˣ) (i : Bool) :=
  Localization.Away (quadraticSignDenominator
    (quadraticOverlapLeftRoot d : QuadraticOverlapRing d)
    (quadraticOverlapRightRoot d : QuadraticOverlapRing d) i)

/-- The first projection on coordinates of a sign chart. -/
def quadraticOverlapLeftMap (d : Rˣ) (i : Bool) :
    QuadraticEtaleRing d →ₐ[R] QuadraticOverlapChartRing d i :=
  (IsScalarTower.toAlgHom R (QuadraticOverlapRing d) (QuadraticOverlapChartRing d i)).comp
    (Algebra.TensorProduct.includeLeft : QuadraticEtaleRing d →ₐ[R] QuadraticOverlapRing d)

/-- The second projection on coordinates of a sign chart. -/
def quadraticOverlapRightMap (d : Rˣ) (i : Bool) :
    QuadraticEtaleRing d →ₐ[R] QuadraticOverlapChartRing d i :=
  (IsScalarTower.toAlgHom R (QuadraticOverlapRing d) (QuadraticOverlapChartRing d i)).comp
    (Algebra.TensorProduct.includeRight : QuadraticEtaleRing d →ₐ[R] QuadraticOverlapRing d)

/-- The two coordinate maps coincide on the equal-root chart. -/
theorem quadraticOverlapMaps_equal (d : Rˣ) :
    quadraticOverlapLeftMap d true = quadraticOverlapRightMap d true := by
  apply (quadraticEtalePair d).hom_ext
  have h := quadraticSignChart_equal
    (quadraticOverlapLeftRoot d : QuadraticOverlapRing d)
    (quadraticOverlapRightRoot d : QuadraticOverlapRing d) (quadraticOverlapRoots_square d)
  change quadraticOverlapLeftMap d true (quadraticEtaleUnit d : QuadraticEtaleRing d) =
    quadraticOverlapRightMap d true (quadraticEtaleUnit d : QuadraticEtaleRing d) at h
  simpa only [quadraticEtaleUnit, IsUnit.unit_spec] using h

/-- The two coordinate maps differ by sign on the opposite-root chart. -/
theorem quadraticOverlapMaps_opposite (d : Rˣ) :
    quadraticOverlapLeftMap d false =
      (quadraticOverlapRightMap d false).comp (quadraticEtaleNeg d) := by
  apply (quadraticEtalePair d).hom_ext
  rw [AlgHom.comp_apply, quadraticEtaleNeg_root, map_neg]
  have h := quadraticSignChart_opposite
    (quadraticOverlapLeftRoot d : QuadraticOverlapRing d)
    (quadraticOverlapRightRoot d : QuadraticOverlapRing d) (quadraticOverlapRoots_square d)
  change quadraticOverlapLeftMap d false (quadraticEtaleUnit d : QuadraticEtaleRing d) =
    -quadraticOverlapRightMap d false (quadraticEtaleUnit d : QuadraticEtaleRing d) at h
  simpa only [quadraticEtaleUnit, IsUnit.unit_spec] using h

/-- The actual open map from a sign chart to the kernel pair. -/
def quadraticOverlapChartMap (d : Rˣ) (i : Bool) :
    Spec (.of (QuadraticOverlapChartRing d i)) ⟶
      pullback (quadraticEtaleCover d) (quadraticEtaleCover d) :=
  quadraticSignInclusion (quadraticOverlapLeftRoot d : QuadraticOverlapRing d)
    (quadraticOverlapRightRoot d : QuadraticOverlapRing d) i ≫ (quadraticOverlapIso d).inv

/-- The first kernel-pair projection is the specified coordinate map. -/
theorem quadraticOverlapChartMap_fst (d : Rˣ) (i : Bool) :
    quadraticOverlapChartMap d i ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (quadraticOverlapLeftMap d i).toRingHom) := by
  dsimp only [quadraticOverlapChartMap, quadraticOverlapIso, quadraticSignInclusion,
    quadraticSignChart, quadraticEtaleCover]
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  rfl

/-- The second kernel-pair projection is the specified coordinate map. -/
theorem quadraticOverlapChartMap_snd (d : Rˣ) (i : Bool) :
    quadraticOverlapChartMap d i ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (quadraticOverlapRightMap d i).toRingHom) := by
  dsimp only [quadraticOverlapChartMap, quadraticOverlapIso, quadraticSignInclusion,
    quadraticSignChart, quadraticEtaleCover]
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  rfl

/-- The projections coincide on the equal-root chart. -/
theorem quadraticOverlapChartMap_equal (d : Rˣ) :
    quadraticOverlapChartMap d true ≫ pullback.fst _ _ =
      quadraticOverlapChartMap d true ≫ pullback.snd _ _ := by
  rw [quadraticOverlapChartMap_fst, quadraticOverlapChartMap_snd, quadraticOverlapMaps_equal]

/-- The projections differ by the sign involution on the opposite-root chart. -/
theorem quadraticOverlapChartMap_opposite (d : Rˣ) :
    quadraticOverlapChartMap d false ≫ pullback.fst _ _ =
      quadraticOverlapChartMap d false ≫ pullback.snd _ _ ≫
        Spec.map (CommRingCat.ofHom (quadraticEtaleNeg d).toRingHom) := by
  rw [quadraticOverlapChartMap_fst, ← Category.assoc, quadraticOverlapChartMap_snd,
    ← Spec.map_comp, quadraticOverlapMaps_opposite]
  rfl


/-- The cover uses the explicit sign-chart inclusions. -/
theorem quadraticOverlapCover_f (d : Rˣ) (h2 : IsUnit (2 : R)) (i : Bool) :
    (quadraticOverlapCover d h2).f i = quadraticOverlapChartMap d i := rfl

/-- For equal squares, the two sign opens are disjoint. -/
theorem quadraticSignOpens_disjoint (u v : R) (h : u ^ 2 = v ^ 2) :
    Disjoint (PrimeSpectrum.basicOpen (u - v)) (PrimeSpectrum.basicOpen (u + v)) := by
  apply disjoint_iff.mpr
  rw [← PrimeSpectrum.basicOpen_mul, quadraticRoots_product u v h, PrimeSpectrum.basicOpen_zero]

end WeierstrassCurve.CubicCharts
