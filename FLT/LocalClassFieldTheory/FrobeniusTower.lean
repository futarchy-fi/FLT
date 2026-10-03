/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.Frobenius

/-!
# Restriction of arithmetic Frobenius in integral DVR towers

The residue embeddings commute with restriction of field automorphisms.
Injectivity of a residue-field embedding then identifies the two q-power maps.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S T K L E : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Field K] [Field L] [Field E]
  [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra T E] [IsFractionRing T E]
  [Algebra R S] [Algebra R T] [Algebra S T]
  [Algebra K L] [Algebra K E] [Algebra L E]
  [Algebra R L] [Algebra R E] [Algebra S E]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [IsScalarTower R K E] [IsScalarTower R T E] [IsScalarTower K L E]
  [IsScalarTower S L E] [IsScalarTower S T E]
  [IsIntegralClosure S R L] [IsIntegralClosure T R E]
  [FiniteDimensional K L] [FiniteDimensional K E] [IsGalois K L] [IsGalois K E]
  [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R T)]
  [IsLocalHom (algebraMap S T)]
  [Algebra.FormallyUnramified R S] [Algebra.FormallyUnramified R T]
  [Finite (ResidueField R)]

/-- Arithmetic Frobenius restricts to arithmetic Frobenius in an unramified
tower over the same base DVR. -/
theorem arithmeticFrobenius_restrict :
    (arithmeticFrobenius R T K E).restrictNormal L = arithmeticFrobenius R S K L := by
  apply arithmeticFrobenius_unique R S K L
  intro x
  let σ := arithmeticFrobenius R T K E
  have hcompat : algebraMap S T (galRestrict R K L S (σ.restrictNormal L) x) =
      galRestrict R K E T σ (algebraMap S T x) := by
    apply IsFractionRing.injective T E
    calc
      algebraMap T E (algebraMap S T (galRestrict R K L S (σ.restrictNormal L) x)) =
          algebraMap L E (algebraMap S L (galRestrict R K L S (σ.restrictNormal L) x)) := by
            simp only [← IsScalarTower.algebraMap_apply]
      _ = algebraMap L E ((σ.restrictNormal L) (algebraMap S L x)) := by
        rw [algebraMap_galRestrict_apply]
      _ = σ (algebraMap L E (algebraMap S L x)) := σ.restrictNormal_commutes L _
      _ = algebraMap T E (galRestrict R K E T σ (algebraMap S T x)) := by
        rw [algebraMap_galRestrict_apply]
        simp only [← IsScalarTower.algebraMap_apply]
  apply (ResidueField.map (algebraMap S T)).injective
  rw [ResidueField.map_residue, map_pow, ResidueField.map_residue, hcompat]
  exact arithmeticFrobenius_residue_integral R T K E (algebraMap S T x)

end LocalClassFieldTheory
