/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedCofinality
public import Mathlib.FieldTheory.Galois.Profinite

/-!
# The profinite Galois group of the unramified union

Specialize the existing topological Galois limit theorem to the constructed
union. Restriction from the chosen separable closure is continuous and
surjective; its kernel fixes every finite unramified stage pointwise.
The limit here is indexed by all finite Galois subextensions of the union.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing

variable (R K C : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

/-- The Galois group of the unramified union is the topological inverse limit
of its finite Galois subextensions. -/
def unramifiedGaloisLimitEquiv :
    Gal(maximalUnramified R K C/K) ≃ₜ*
      ↥(ProfiniteGrp.limit
        (InfiniteGalois.asProfiniteGaloisGroupFunctor K (maximalUnramified R K C))) := by
  let := maximalUnramified_isGalois R K C
  exact InfiniteGalois.continuousMulEquivToLimit K (maximalUnramified R K C)

/-- Restriction from the chosen separable closure to the unramified union. -/
def unramifiedRestriction : Gal(C/K) →* Gal(maximalUnramified R K C/K) := by
  let := maximalUnramified_normal R K C
  exact AlgEquiv.restrictNormalHom (maximalUnramified R K C)

/-- Restriction is continuous for the actual Krull topologies. -/
theorem unramifiedRestriction_continuous : Continuous (unramifiedRestriction R K C) := by
  let := maximalUnramified_normal R K C
  exact InfiniteGalois.restrictNormalHom_continuous (maximalUnramified R K C)

/-- Every automorphism of the unramified union extends to the separable closure. -/
theorem unramifiedRestriction_surjective :
    Function.Surjective (unramifiedRestriction R K C) := by
  let : IsSepClosure K C := ⟨inferInstance, inferInstance⟩
  let := maximalUnramified_normal R K C
  exact AlgEquiv.restrictNormalHom_surjective _

/-- The restriction kernel is exactly the automorphisms fixing every finite stage. -/
theorem mem_unramifiedRestriction_ker_iff (σ : Gal(C/K)) :
    σ ∈ (unramifiedRestriction R K C).ker ↔
      ∀ (n : ℕ+) (x : C), x ∈ unramifiedStage R K C n → σ x = x := by
  let := maximalUnramified_normal R K C
  change AlgEquiv.restrictNormal σ (maximalUnramified R K C) = 1 ↔ _
  rw [AlgEquiv.restrictNormal_eq_one_iff]
  constructor
  · intro h n x hx
    exact h x (unramifiedStage_le_maximalUnramified R K C n hx)
  · intro h x hx
    obtain ⟨n, hn⟩ := (mem_maximalUnramified_iff R K C x).mp hx
    exact h n x hn

end LocalClassFieldTheory
