/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceIncidentPatchRoutes

/-!
# Symmetric common occurrence families

A common occurrence consists of a literal overlap label and one occurrence
in each ambient chart. Swapping charts preserves that label exactly.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe v w z

variable {ι : Type v} {κ : Type w} {J : ι → Type z} (dst : ∀ i, J i → κ)

/-- All shared overlap labels together with their two literal occurrences. -/
abbrev PrincipalOccurrenceCommon (i t : ι) :=
  Σ j : κ, {k : J i // dst i k = j} × {l : J t // dst t l = j}

/-- The same common overlap with its ambient charts exchanged. -/
def principalOccurrenceCommonSwap (i t : ι) :
    PrincipalOccurrenceCommon dst i t ≃ PrincipalOccurrenceCommon dst t i where
  toFun p := ⟨p.1, p.2.2, p.2.1⟩
  invFun p := ⟨p.1, p.2.2, p.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exchanging charts twice recovers the literal occurrence pair. -/
@[simp] theorem principalOccurrenceCommonSwap_swap (i t : ι)
    (p : PrincipalOccurrenceCommon dst i t) :
    principalOccurrenceCommonSwap dst t i (principalOccurrenceCommonSwap dst i t p) = p := rfl

/-- Every occurrence appears in the diagonal common family. -/
def principalOccurrenceCommonDiagonal (i : ι) (k : J i) :
    PrincipalOccurrenceCommon dst i i := ⟨dst i k, ⟨k, rfl⟩, ⟨k, rfl⟩⟩

/-- Finite occurrence data gives finite symmetric common families. -/
instance principalOccurrenceCommon_finite [Finite κ] [∀ i, Finite (J i)] (i t : ι) :
    Finite (PrincipalOccurrenceCommon dst i t) := inferInstance

end FLT.Mazur.FiniteTypeRelationModel
