/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedBaseChangeEmbedding
public import FLT.LocalClassFieldTheory.UnramifiedUnion

/-!
# Inclusion of maximal unramified unions under local base change

Every degree-n stage over the original base embeds into the degree-n
stage over the new base. Normality in the common separable overfield turns
that embedding into literal containment, hence gives the inclusion of unions.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S K L C : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [Field C] [Algebra L C] [Algebra K C] [Algebra R C] [Algebra S C]
  [IsScalarTower K L C] [IsScalarTower R K C] [IsScalarTower R L C]
  [IsScalarTower S L C] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [Algebra.IsSeparable L C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

/-- Base change places each original unramified stage in the new stage of the same degree. -/
theorem unramifiedStage_baseChange (n : ℕ+) :
    unramifiedStage R K C n ≤ (unramifiedStage S L C n).restrictScalars K := by
  let E := unramifiedStage R K C n
  let F := unramifiedStage S L C n
  have hE := unramifiedStage_isUnramified R K C n
  have hF := unramifiedStage_isUnramified S L C n
  let : Normal K E := hE.normal
  let : IsScalarTower R K F := IsScalarTower.of_algebraMap_eq fun r => by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply R K C r
  let : IsScalarTower R S F := IsScalarTower.of_algebraMap_eq fun r => by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply R S C r
  obtain ⟨f⟩ := unramifiedBaseChangeEmbedding (R := R) (S := S) (K := K) (L := L)
    (E := E) (F := F) hE hF (by simp only [E, F, finrank_unramifiedStage, dvd_refl])
  intro x hx
  change x ∈ E at hx
  rw [← AlgHom.fieldRange_of_normal ((F.val.restrictScalars K).comp f)] at hx
  obtain ⟨y, rfl⟩ := hx
  exact (f y).property

/-- The maximal unramified union of the original base is contained in the new union. -/
theorem maximalUnramified_baseChange_le :
    maximalUnramified R K C ≤ (maximalUnramified S L C).restrictScalars K := by
  intro x hx
  obtain ⟨n, hn⟩ := (mem_maximalUnramified_iff R K C x).mp hx
  exact unramifiedStage_le_maximalUnramified S L C n (unramifiedStage_baseChange R S K L C n hn)

/-- The actual field inclusion between the two maximal unramified unions. -/
def maximalUnramifiedBaseChange :
    maximalUnramified R K C →ₐ[K] maximalUnramified S L C :=
  IntermediateField.inclusion (maximalUnramified_baseChange_le R S K L C)

/-- The inclusion preserves the element of the common separable overfield. -/
theorem maximalUnramifiedBaseChange_apply (x : maximalUnramified R K C) :
    (maximalUnramifiedBaseChange R S K L C x : C) = (x : C) := rfl

end LocalClassFieldTheory
