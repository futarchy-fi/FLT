/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionRank
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! # Finite free torsion over local integral bases -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
open Module IsLocalRing
@[expose] public noncomputable section
namespace WeierstrassCurve.CubicCharts
universe u
/-- Equal residual and faithful-field dimensions make a finite module over a local ring free. -/
theorem free_of_residue_generic_finrank_eq
    (R M K : Type u) [CommRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Field K] [Algebra R K] [FaithfulSMul R K]
    (h : Module.finrank (ResidueField R) ((ResidueField R) ⊗[R] M) =
      Module.finrank K (K ⊗[R] M)) : Module.Free R M := by
  classical
  let k := ResidueField R
  let d := Module.finrank k (k ⊗[R] M)
  let b := Module.finBasis k (k ⊗[R] M)
  have hs : Function.Surjective (TensorProduct.mk R k M 1) :=
    TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective
  choose v hv using fun i : Fin d => hs (b i)
  have hsp : Submodule.span R (Set.range v) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis v b hv
  have hg : Submodule.span K (Set.range (fun i => (1 : K) ⊗ₜ[R] v i)) = ⊤ := by
    rw [show Set.range (fun i => (1 : K) ⊗ₜ[R] v i) =
      TensorProduct.mk R K M 1 '' Set.range v from Set.range_comp (TensorProduct.mk R K M 1) v,
      ← Submodule.baseChange_span, hsp, Submodule.baseChange_top]
  have hi : LinearIndependent K (fun i => (1 : K) ⊗ₜ[R] v i) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hg.ge (by simpa [d, k] using h)
  have hir : LinearIndependent R v :=
    LinearIndependent.of_comp (TensorProduct.mk R K M 1) (hi.restrict_scalars' R)
  exact Module.Free.of_basis (Basis.mk hir hsp.ge)

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]
/-- An invertible torsion order gives dimension n² over every field algebra. -/
theorem torsionCoordinate_field_finrank_of_isUnit (n : ℕ) [NeZero n]
    (K : Type u) [Field K] [Algebra R K] (hn : IsUnit (n : K)) :
    Module.finrank K (K ⊗[R] torsionCoordinateRing W n) = n ^ 2 := by
  let Ω := AlgebraicClosure K
  apply torsionCoordinate_field_finrank W n K Ω
  simpa using (hn.map (algebraMap K Ω)).ne_zero

/-- Invertible-order torsion is finite free over a local integral coefficient ring. -/
theorem torsionCoordinate_local_free [IsLocalRing R] [IsDomain R]
    (n : ℕ) [NeZero n] (hn : IsUnit (n : R)) :
    Module.Free R (torsionCoordinateRing W n) := by
  have : Module.Finite R (torsionCoordinateRing W n) := torsionCoordinateRing_finite W n
  apply free_of_residue_generic_finrank_eq R (torsionCoordinateRing W n) (FractionRing R)
  exact (torsionCoordinate_field_finrank_of_isUnit W n (ResidueField R)
    (by simpa using hn.map (algebraMap R (ResidueField R)))).trans
      (torsionCoordinate_field_finrank_of_isUnit W n (FractionRing R)
        (by simpa using hn.map (algebraMap R (FractionRing R)))).symm


/-- Over a local integral base, invertible-order torsion has an étale coordinate algebra. -/
theorem torsionCoordinate_local_etale [IsLocalRing R] [IsDomain R]
    (n : ℕ) [NeZero n] (hn : IsUnit (n : R)) :
    Algebra.Etale R (torsionCoordinateRing W n) := by
  have : Module.Finite R (torsionCoordinateRing W n) := torsionCoordinateRing_finite W n
  have : Module.Free R (torsionCoordinateRing W n) := torsionCoordinate_local_free W n hn
  have : Algebra.FormallyUnramified R (torsionCoordinateRing W n) :=
    torsionCoordinate_formallyUnramified W n hn
  have : Algebra.FinitePresentation R (torsionCoordinateRing W n) :=
    (Algebra.FinitePresentation.of_finiteType (R := R)).mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

end WeierstrassCurve.CubicCharts
