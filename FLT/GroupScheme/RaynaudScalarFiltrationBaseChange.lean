/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudScalarFiltration
public import FLT.GroupScheme.FiniteFlatRestrictedScalarExtension

/-!
# Scalar filtrations survive actual model base change

The restricted tensor-product model retains the underlying point groups,
exact maps, and scalar fields. The new Galois action is restriction along
the actual absolute-Galois homomorphism, so it still commutes with scalars.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K]
  (S L : Type) [CommRing S] [Field L] [PerfectField L] [Algebra R S]
  [Algebra R L] [Algebra S L] [IsScalarTower R S L]
  [Algebra K L] [IsScalarTower R K L]

/-- Restriction of the actual point action preserves a scalar filtration of any length. -/
theorem FF.HasScalarFiltration.restrictScalars {p n : ℕ} {X : FF R K}
    (hX : X.HasScalarFiltration p n) :
    (X.restrictedScalarExtension S L).HasScalarFiltration p n := by
  induction n generalizing X with
  | zero => exact hX
  | succ n ih =>
    obtain ⟨A, Q, i, q, hi, hq, hex, F, hF, hfin, hp, hm, hc, hd, hA⟩ := hX
    let : Module F (Q.restrictedScalarExtension S L).Points := inferInstanceAs (Module F Q.Points)
    let : SMulCommClass F (AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
        (Q.restrictedScalarExtension S L).Points := by
      constructor
      intro a σ x
      exact @smul_comm F (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) Q.Points
        _ _ hc a (Field.absoluteGaloisGroup.map (algebraMap K L) σ) x
    refine ⟨A.restrictedScalarExtension S L, Q.restrictedScalarExtension S L,
      i.restrictScalars S L, q.restrictScalars S L, hi, hq, hex,
      F, hF, hfin, hp, inferInstance, inferInstance, hd, ih hA⟩

end ThreeAdicPlan
