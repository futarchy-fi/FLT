/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineScalarFiberComparison
public import FLT.Mazur.ReducedGeometricFiberFlat
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Etale.Field

/-!
# Constant geometric point count for finite unramified schemes

Over a reduced affine base, constant geometric cardinality forces a finite
formally unramified morphism to be flat. With finite presentation it is etale.
Reducedness of the geometric fibers turns point counts into dimensions;
reducedness of the base then removes possible module relations.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.FiniteUnramifiedConstantFiber

universe u
variable {R : Type u} [CommRing R] [_root_.IsReduced R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) [IsFinite f] [FormallyUnramified f]

/-- Constant geometric cardinality makes a finite unramified morphism flat over a reduced base. -/
theorem flat_of_geometric_card (n : ℕ)
    (hc : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      Nat.card (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) : Scheme.{u}) = n) :
    Flat f := by
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let _ := (AffineScalarFiberComparison.scalarMap f).toAlgebra
  let _ : Module.Finite R Γ(X, ⊤) := AffineScalarFiberComparison.scalarMap_finite f
  let _ : Algebra.FormallyUnramified R Γ(X, ⊤) :=
    AffineScalarFiberComparison.scalarMap_formallyUnramified f
  apply AffineScalarFiberComparison.flat_of_scalarMap f
  change Module.Flat R Γ(X, ⊤)
  apply ReducedGeometricFiberFlat.flat_of_constant_geometric_dimension n
  intro K _ _ _
  let B := K ⊗[R] Γ(X, ⊤)
  let _ : Algebra.FormallyEtale K B :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field K B
  let _ : IsArtinianRing B := isArtinian_of_tower K inferInstance
  let _ : Fintype (PrimeSpectrum B) := Fintype.ofFinite _
  have he : Module.finrank K B = Nat.card (PrimeSpectrum B) := by
    rw [(Algebra.FormallyEtale.equivPiOfIsSepClosed K B).toLinearEquiv.finrank_eq,
      Module.finrank_pi]
    simp
  exact he.trans ((AffineScalarFiberComparison.fiber_card_tensor f K).trans (hc K))

/-- Finite presentation upgrades the resulting flat unramified morphism to etale. -/
theorem etale_of_geometric_card [LocallyOfFinitePresentation f] (n : ℕ)
    (hc : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      Nat.card (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) : Scheme.{u}) = n) :
    Etale f := by
  let _ := flat_of_geometric_card f n hc
  exact Etale.of_formallyUnramified_of_flat f

end FLT.Mazur.FiniteUnramifiedConstantFiber
