/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudInertiaScalarFiltration
public import FLT.GroupScheme.RaynaudScalarFilteredExtension

/-!
# Prescribed extension from a model compatible with local inertia

The continuous inertia representation and its agreement with the actual
Galois action construct the scalar filtration. Integral dévissage then gives
every prescribed extension, without scalar or filtration data as inputs.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open NumberField IsLocalRing
open scoped TensorProduct

variable {R K L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field L] [NumberField L]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
  [CharP (ResidueField (v.adicCompletionIntegers L)) p]
  (X : FF R K) [Module (ZMod p) X.Points]
  (ρ : Representation (ZMod p) (localInertiaGroup v) X.Points) (hρ : ρ.IsDiscreteContinuous)
  (ha : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∃ t : localInertiaGroup v,
    ∀ x : X.Points, σ • x = ρ t x)
  (he : RaynaudParameters.order (p : R) < p - 1)

include hρ ha he in
/-- Deriving the scalar filtration from inertia suffices for each prescribed integral extension. -/
theorem extend_from_inertia_agreement (Y : FF R K) (f : GenericGaloisHom X Y) :
    ∃! g : ModelHom X Y, genericHom g = f := by
  obtain ⟨n, hX⟩ := exists_scalarFiltration_of_inertia_agreement v p X ρ hρ ha
  exact extend_from_scalar_filtered_model p he hX f

include hρ ha he in
/-- The prescribed coordinate pullback is integral, with all scalar factors derived from inertia. -/
theorem GenericGaloisHom.integral_of_inertia_agreement {Y : FF R K}
    (f : GenericGaloisHom X Y) (y : Y.CoordinateRing) :
    ∃ x : X.CoordinateRing, f.toBialgHom (1 ⊗ₜ[R] y) = 1 ⊗ₜ[R] x := by
  obtain ⟨n, hX⟩ := exists_scalarFiltration_of_inertia_agreement v p X ρ hρ ha
  exact f.integral_of_scalarFiltration p he hX y

end ThreeAdicPlan
