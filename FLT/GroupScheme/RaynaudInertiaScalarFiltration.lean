/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCompatibleSubquotients
public import FLT.GroupScheme.RaynaudScalarFiltration

/-!
# Construction of scalar filtrations from local inertia

Induction on the actual finite point cardinality repeatedly takes a maximal
proper inertia subrepresentation. Its simple quotient supplies a derived
scalar field, and the compatible kernel is strictly smaller.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open NumberField IsLocalRing

variable {R K L : Type} [CommRing R] [Field K] [Field L] [NumberField L]
  [Algebra R K] [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField (v.adicCompletionIntegers L)) p]
  (X : FF R K) [Module (ZMod p) X.Points]

/-- The actual compatible inertia action constructs a scalar filtration of the model. -/
theorem exists_scalarFiltration_of_inertia_agreement
    (ρ : Representation (ZMod p) (localInertiaGroup v) X.Points) (hρ : ρ.IsDiscreteContinuous)
    (ha : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∃ t : localInertiaGroup v,
      ∀ x : X.Points, σ • x = ρ t x) : ∃ n, X.HasScalarFiltration p n := by
  induction hn : Nat.card X.Points using Nat.strong_induction_on generalizing X with
  | h n ih =>
    by_cases hX : Subsingleton X.Points
    · let : Subsingleton X.Points := hX
      exact ⟨0, Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩⟩
    · let : Nontrivial X.Points := not_subsingleton_iff_nontrivial.mp hX
      obtain ⟨S, Q, i, q, hi, hq, hex, hmS, ρS, hρS, haS, hlt,
          F, hF, hfin, hp, hmQ, hcomm, hdim⟩ :=
        exists_compatible_scalar_quotient v p X ρ hρ ha
      obtain ⟨m, hm⟩ := ih (Nat.card S.Points) (hlt.trans_eq hn) S ρS hρS haS rfl
      exact ⟨m + 1, S, Q, i, q, hi, hq, hex, F, hF, hfin, hp, hmQ, hcomm, hdim, hm⟩

end ThreeAdicPlan
