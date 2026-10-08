/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreCyclicBraid

/-! # A common coefficient cover for the mixed Legendre relation

The tensor product of three quadratic covers carries compatible roots of
-1, lambda and 1-lambda. It is finite, etale and surjective, and realizes
the mixed coordinate relation. No domain instance is asserted: applying
the cyclic construction and descending its relation require further proofs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]

/-- The coefficient ring of the fiber product of three quadratic covers. -/
abbrev QuadraticTripleRing (d e f : Rˣ) :=
  (QuadraticEtaleRing d ⊗[R] QuadraticEtaleRing e) ⊗[R] QuadraticEtaleRing f

/-- The first quadratic factor included in the common coefficient ring. -/
def quadraticTripleFirstMap (d e f : Rˣ) :
    QuadraticEtaleRing d →ₐ[R] QuadraticTripleRing d e f :=
  Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeLeft
/-- The second quadratic factor included in the common coefficient ring. -/
def quadraticTripleSecondMap (d e f : Rˣ) :
    QuadraticEtaleRing e →ₐ[R] QuadraticTripleRing d e f :=
  Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeRight
/-- The third quadratic factor included in the common coefficient ring. -/
def quadraticTripleThirdMap (d e f : Rˣ) :
    QuadraticEtaleRing f →ₐ[R] QuadraticTripleRing d e f :=
  Algebra.TensorProduct.includeRight

/-- The first quadratic unit root on the common cover. -/
def quadraticTripleFirstRoot (d e f : Rˣ) : (QuadraticTripleRing d e f)ˣ :=
  Units.map (quadraticTripleFirstMap d e f).toMonoidHom (quadraticEtaleUnit d)
/-- The second quadratic unit root on the common cover. -/
def quadraticTripleSecondRoot (d e f : Rˣ) : (QuadraticTripleRing d e f)ˣ :=
  Units.map (quadraticTripleSecondMap d e f).toMonoidHom (quadraticEtaleUnit e)
/-- The third quadratic unit root on the common cover. -/
def quadraticTripleThirdRoot (d e f : Rˣ) : (QuadraticTripleRing d e f)ˣ :=
  Units.map (quadraticTripleThirdMap d e f).toMonoidHom (quadraticEtaleUnit f)

private theorem quadraticRootImage_square {S : Type u} [CommRing S] [Algebra R S]
    (d : Rˣ) (g : QuadraticEtaleRing d →ₐ[R] S) :
    ((Units.map g.toMonoidHom (quadraticEtaleUnit d) : Sˣ) : S) ^ 2 =
      algebraMap R S (d : R) := by
  change g (quadraticEtaleUnit d : QuadraticEtaleRing d) ^ 2 = _
  rw [← map_pow, quadraticEtaleUnit_square, AlgHom.commutes]

theorem quadraticTripleFirstRoot_square (d e f : Rˣ) :
    (quadraticTripleFirstRoot d e f : QuadraticTripleRing d e f) ^ 2 =
      algebraMap R _ (d : R) := quadraticRootImage_square d _
theorem quadraticTripleSecondRoot_square (d e f : Rˣ) :
    (quadraticTripleSecondRoot d e f : QuadraticTripleRing d e f) ^ 2 =
      algebraMap R _ (e : R) := quadraticRootImage_square e _
theorem quadraticTripleThirdRoot_square (d e f : Rˣ) :
    (quadraticTripleThirdRoot d e f : QuadraticTripleRing d e f) ^ 2 =
      algebraMap R _ (f : R) := quadraticRootImage_square f _

variable (d e f : Rˣ) [Fact (IsUnit (2 : R))]
instance quadraticTripleFinite : Module.Finite R (QuadraticTripleRing d e f) := by
  infer_instance
instance quadraticTripleFree : Module.Free R (QuadraticTripleRing d e f) := by
  infer_instance
instance quadraticTripleNontrivial [Nontrivial R] :
    Nontrivial (QuadraticTripleRing d e f) := by infer_instance
instance quadraticTripleNoetherian [IsNoetherianRing R] :
    IsNoetherianRing (QuadraticTripleRing d e f) :=
  IsNoetherianRing.of_finite R _
instance quadraticTripleEtale : Algebra.Etale R (QuadraticTripleRing d e f) := by
  let : Algebra.Etale R (QuadraticEtaleRing d ⊗[R] QuadraticEtaleRing e) :=
    .comp R (QuadraticEtaleRing d) _
  exact .comp R (QuadraticEtaleRing d ⊗[R] QuadraticEtaleRing e) _

/-- The common quadratic coefficient cover over the original base. -/
def quadraticTripleCover :
    Spec (.of (QuadraticTripleRing d e f)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (QuadraticTripleRing d e f)))

instance quadraticTripleCoverEtale : Etale (quadraticTripleCover d e f) := by
  rw [quadraticTripleCover, HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.mpr inferInstance
instance quadraticTripleCoverFinite : IsFinite (quadraticTripleCover d e f) := by
  rw [quadraticTripleCover, IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance
instance quadraticTripleCoverSurjective [Nontrivial R] :
    Surjective (quadraticTripleCover d e f) := by
  constructor
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := R) (B := QuadraticTripleRing d e f)


/-- The invertible complement of the universal Legendre parameter. -/
def legendreComplementUnit (p : ℕ) : (LegendreBase p)ˣ :=
  (legendreSwapParameter_units p).1.unit

@[simp]
theorem legendreComplementUnit_val (p : ℕ) :
    (legendreComplementUnit p : LegendreBase p) = 1 - legendreParameter p :=
  IsUnit.unit_spec _

/-- The common coefficient ring carrying the three roots for the mixed relation. -/
abbrev LegendreBraidRing (p : ℕ) :=
  QuadraticTripleRing (-1 : (LegendreBase p)ˣ) (legendreParameterUnit p)
    (legendreComplementUnit p)

/-- The chosen square root of minus one on the common Legendre cover. -/
def legendreBraidMinusOneRoot (p : ℕ) : (LegendreBraidRing p)ˣ :=
  quadraticTripleFirstRoot (-1) (legendreParameterUnit p) (legendreComplementUnit p)
/-- The chosen square root of lambda on the common Legendre cover. -/
def legendreBraidParameterRoot (p : ℕ) : (LegendreBraidRing p)ˣ :=
  quadraticTripleSecondRoot (-1) (legendreParameterUnit p) (legendreComplementUnit p)
/-- The chosen square root of one minus lambda on the common Legendre cover. -/
def legendreBraidComplementRoot (p : ℕ) : (LegendreBraidRing p)ˣ :=
  quadraticTripleThirdRoot (-1) (legendreParameterUnit p) (legendreComplementUnit p)

theorem legendreBraidMinusOneRoot_square (p : ℕ) :
    (legendreBraidMinusOneRoot p : LegendreBraidRing p) ^ 2 = -1 := by
  rw [legendreBraidMinusOneRoot, quadraticTripleFirstRoot_square]
  simp only [Units.val_neg, Units.val_one, map_neg, map_one]
theorem legendreBraidParameterRoot_square (p : ℕ) :
    (legendreBraidParameterRoot p : LegendreBraidRing p) ^ 2 =
      algebraMap (LegendreBase p) (LegendreBraidRing p) (legendreParameter p) := by
  simp [legendreBraidParameterRoot, quadraticTripleSecondRoot_square]
theorem legendreBraidComplementRoot_square (p : ℕ) :
    (legendreBraidComplementRoot p : LegendreBraidRing p) ^ 2 =
      1 - algebraMap (LegendreBase p) (LegendreBraidRing p) (legendreParameter p) := by
  rw [legendreBraidComplementRoot, quadraticTripleThirdRoot_square,
    legendreComplementUnit_val, map_sub, map_one]

/-- The finite etale common cover used for the mixed Legendre relation. -/
def legendreBraidCover (p : ℕ) :
    Spec (.of (LegendreBraidRing p)) ⟶ Spec (.of (LegendreBase p)) :=
  quadraticTripleCover (-1) (legendreParameterUnit p) (legendreComplementUnit p)

instance legendreBraidCoverEtale (p : ℕ) : Etale (legendreBraidCover p) := by
  dsimp [legendreBraidCover]
  infer_instance
instance legendreBraidCoverFinite (p : ℕ) : IsFinite (legendreBraidCover p) := by
  dsimp [legendreBraidCover]
  infer_instance
instance legendreBraidCoverSurjective (p : ℕ) [NeZero p] :
    Surjective (legendreBraidCover p) := by
  dsimp [legendreBraidCover]
  infer_instance

instance legendreBraidLevelUnit (p : ℕ) : Fact (IsUnit (p : LegendreBraidRing p)) :=
  ⟨by simpa only [map_natCast] using
    (legendreBase_units p).2.1.map (algebraMap (LegendreBase p) (LegendreBraidRing p))⟩

theorem legendreBraidCover_coordinate_relation (p : ℕ) :
    legendreSwapChange (legendreBraidMinusOneRoot p) *
      legendreReciprocalChange (legendreBraidComplementRoot p) *
        legendreSwapChange (legendreBraidMinusOneRoot p) =
    legendreReciprocalChange (legendreBraidRoot (legendreBraidMinusOneRoot p)
      (legendreBraidComplementRoot p) (legendreBraidParameterRoot p)) *
        legendreSwapChange (legendreBraidMinusOneRoot p) *
          legendreReciprocalChange (legendreBraidParameterRoot p) := by
  apply legendreCoordinate_braid
  · exact legendreBraidMinusOneRoot_square p
  · rw [legendreBraidComplementRoot_square, legendreBraidParameterRoot_square]
    ring

end WeierstrassCurve.CubicCharts
