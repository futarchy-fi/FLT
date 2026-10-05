/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicAffineDomain

/-! # Integral Weierstrass schemes

The infinity chart embeds into the integral overlap. Together with the ordinary
chart, this proves that the glued cubic over a domain is integral and connected. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Put the infinity coordinate u in the outer polynomial variable. -/
def infinityCoordinates : MvPolynomial (Fin 2) R ≃ₐ[R] Polynomial (Polynomial R) :=
  (finSuccEquiv R 1).trans (Polynomial.mapAlgEquiv (uniqueAlgEquiv R (Fin 1)))

@[simp] theorem infinityCoordinates_C (r : R) :
    infinityCoordinates (R := R) (C r) = Polynomial.C (Polynomial.C r) :=
  (infinityCoordinates (R := R)).commutes r

@[simp] theorem infinityCoordinates_X_zero :
    infinityCoordinates (R := R) (X 0) = Polynomial.X := by
  simp [infinityCoordinates, finSuccEquiv_X_zero]

@[simp] theorem infinityCoordinates_X_one :
    infinityCoordinates (R := R) (X 1) = Polynomial.C Polynomial.X := by
  simp only [infinityCoordinates, AlgEquiv.trans_apply]
  rw [show (1 : Fin 2) = (0 : Fin 1).succ from rfl, finSuccEquiv_X_succ]
  change Polynomial.map (uniqueAlgEquiv R (Fin 1)).toRingHom (Polynomial.C (X 0)) = _
  rw [Polynomial.map_C]
  exact congrArg Polynomial.C (eval₂_X _ _ _)

/-- The infinity equation, monic in u, with coefficients in R[v]. -/
def infinityPolynomial : Polynomial (Polynomial R) :=
  Polynomial.X ^ 3 +
    (Polynomial.C (Polynomial.C W.a₂ * Polynomial.X) * Polynomial.X ^ 2 +
    Polynomial.C (Polynomial.C W.a₄ * Polynomial.X ^ 2 -
      Polynomial.C W.a₁ * Polynomial.X) * Polynomial.X +
    Polynomial.C (Polynomial.C W.a₆ * Polynomial.X ^ 3 -
      Polynomial.C W.a₃ * Polynomial.X ^ 2 - Polynomial.X))

theorem infinityPolynomial_monic : (infinityPolynomial W).Monic := by
  unfold infinityPolynomial
  apply Polynomial.monic_X_pow_add
  compute_degree
  norm_num

theorem infinityCoordinates_equation :
    infinityCoordinates (equation W true) = -infinityPolynomial W := by
  simp only [equation, ite_eq_left, InfinityChart.equation, map_sub, map_add, map_mul,
    map_pow, infinityCoordinates_C, infinityCoordinates_X_zero, infinityCoordinates_X_one]
  simp only [infinityPolynomial, map_sub, map_mul, map_pow]
  ring

/-- The infinity chart as a monic cubic extension of the v-line. -/
def infinityCoordinateRingEquiv :
    Ring W true ≃ₐ[R] AdjoinRoot (infinityPolynomial W) :=
  Ideal.quotientEquivAlg (Ideal.span {equation W true}) _
    (infinityCoordinates (R := R)) (by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {infinityPolynomial W} =
        Ideal.span {infinityCoordinates (equation W true)}
      rw [infinityCoordinates_equation, Ideal.span_singleton_neg])

@[simp] theorem infinityCoordinateRingEquiv_coord_one :
    infinityCoordinateRingEquiv W (coord W true 1) =
      algebraMap (Polynomial R) (AdjoinRoot (infinityPolynomial W)) Polynomial.X := by
  change Ideal.Quotient.mk _ (infinityCoordinates (X 1)) = _
  rw [infinityCoordinates_X_one]
  rfl

/-- Multiplication by the overlap coordinate is injective on the infinity chart. -/
theorem infinity_coord_one_mem_nonZeroDivisors [IsDomain R] :
    coord W true 1 ∈ nonZeroDivisors (Ring W true) := by
  let : Module.Free (Polynomial R) (AdjoinRoot (infinityPolynomial W)) :=
    (infinityPolynomial_monic W).free_adjoinRoot
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  apply (infinityCoordinateRingEquiv W).injective
  have h := congrArg (infinityCoordinateRingEquiv W) hx
  rw [map_mul, infinityCoordinateRingEquiv_coord_one, map_zero,
    ← Algebra.smul_def] at h
  simpa only [map_zero] using (smul_eq_zero.mp h).resolve_left Polynomial.X_ne_zero

/-- Localization into the overlap does not identify distinct infinity-chart elements. -/
theorem infinity_to_overlap_injective [IsDomain R] :
    Function.Injective (algebraMap (Ring W true) (Overlap W true)) :=
  IsLocalization.injective (Overlap W true)
    (Submonoid.powers_le.mpr (infinity_coord_one_mem_nonZeroDivisors W))

/-- The infinity chart embeds into its integral overlap. -/
instance infinityRing_isDomain [IsDomain R] : IsDomain (Ring W true) :=
  (infinity_to_overlap_injective W).isDomain

/-- The infinity chart is irreducible over any integral coefficient ring. -/
instance infinityChart_irreducibleSpace [IsDomain R] : IrreducibleSpace (chart W true) :=
  inferInstanceAs (IrreducibleSpace (PrimeSpectrum (Ring W true)))

/-- The overlap is dense in the infinity chart. -/
theorem infinityOverlap_denseRange [IsDomain R] : DenseRange (overlapInclusion W true) :=
  (overlapInclusion W true).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _

/-- The ordinary affine chart is dense in the entire glued cubic. -/
theorem affineChart_denseRange [IsDomain R] : DenseRange (affineChart W) := by
  have hd : DenseRange (overlapRight W) :=
    (overlapRight W).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _
  intro x
  rcases charts_cover W x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact subset_closure ⟨y, rfl⟩
  · apply hd.induction_on (p := fun z ↦
      infinityChart W z ∈ closure (Set.range (affineChart W))) y
      (isClosed_closure.preimage (infinityChart W).continuous)
    intro z
    have hz := congrArg (fun f ↦ f z) (overlap_condition W)
    change affineChart W (overlapInclusion W false z) =
      infinityChart W (overlapRight W z) at hz
    rw [← hz]
    exact subset_closure ⟨_, rfl⟩

/-- The glued Weierstrass cubic is irreducible over any domain, even when singular. -/
instance scheme_irreducibleSpace [IsDomain R] : IrreducibleSpace (scheme W) := by
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set (scheme W))
  have h := (IrreducibleSpace.isIrreducible_univ (chart W false)).image
    (affineChart W) (affineChart W).continuous.continuousOn
  rw [Set.image_univ] at h
  simpa only [(affineChart_denseRange W).closure_range] using h.closure

/-- In particular, the glued Weierstrass cubic over a domain is connected. -/
instance scheme_connectedSpace [IsDomain R] : ConnectedSpace (scheme W) := inferInstance

/-- Both integral charts give a reduced glued scheme. -/
instance scheme_isReduced [IsDomain R] : AlgebraicGeometry.IsReduced (scheme W) := by
  let : ∀ b, AlgebraicGeometry.IsReduced ((sourceOpenCover W).X b) := by
    intro b
    cases b <;> exact inferInstanceAs (AlgebraicGeometry.IsReduced (Spec _))
  exact AlgebraicGeometry.IsReduced.of_openCover _ (sourceOpenCover W)

/-- The glued Weierstrass cubic over a domain is an integral scheme. -/
instance scheme_isIntegral [IsDomain R] : AlgebraicGeometry.IsIntegral (scheme W) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

end WeierstrassCurve.CubicCharts
