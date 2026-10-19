/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.FiniteExtensionPerfectDVRModel
public import FLT.Mazur.FiniteExtensionValuationSubring

/-!
# A perfect-residue valuation subring in the prescribed finite extension

Realize the constructed DVR in the same generic field. Its perfect residue
field and exact restriction to the original valuation subring are proved.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteExtensionPerfectValuationSubring
open IsLocalRing
variable {K L : Type} [Field K] [Field L]
  [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
  (A : ValuationSubring K) [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]

/-- Construct the extended DVR with perfect residue and the exact original restriction. -/
theorem exists_extension :
    ∃ (B : ValuationSubring L) (_ : IsDiscreteValuationRing B) (_ : IsNoetherianRing B)
      (_ : PerfectField (ResidueField B)) (φ : A →+* B), IsLocalHom φ ∧
      (∀ a : A, (φ a : L) = algebraMap K L a) ∧ B.comap (algebraMap K L) = A := by
  obtain ⟨S, hS, domS, dvrS, aS, aSL, tower, frac, perf, hlocal⟩ :=
    FiniteExtensionPerfectDVRModel.exists_model A K L
  let _ := hS
  let _ := domS
  let _ := dvrS
  let _ := aS
  let _ := aSL
  let _ := tower
  let _ := frac
  let _ := perf
  let _ := hlocal
  let B := fractionValuationSubring S L
  let _ : IsDiscreteValuationRing B := fractionValuationSubring_isDiscreteValuationRing S L
  let _ : PerfectField (ResidueField B) :=
    PerfectField.of_ringEquiv (ResidueField.mapEquiv (fractionValuationEquiv S L))
  let φ : A →+* B := fractionValuationBaseMap
  have hφ (a : A) : (φ a : L) = algebraMap K L a :=
    fractionValuationBaseMap_coe a
  refine ⟨B, inferInstance, inferInstance, inferInstance, φ, inferInstance, hφ, ?_⟩
  exact FiniteExtensionValuationSubring.comap_eq A B (algebraMap K L) φ hφ

end FLT.Mazur.FiniteExtensionPerfectValuationSubring
