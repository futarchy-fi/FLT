/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedInertiaConverse
public import FLT.LocalClassFieldTheory.UnramifiedGaloisLimit
public import FLT.AbsoluteGaloisGroup.TameCharacter

/-!
# The local inertia kernel of the constructed unramified union

Inside the algebraic closure of a number-field completion, the constructed
union is exactly the fixed field of the existing valuation inertia subgroup.
Closedness of inertia then identifies the restriction kernel itself.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing NumberField

variable {F : Type} [Field F] [NumberField F]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

local notation "K" => v.adicCompletion F
local notation "R" => v.adicCompletionIntegers F
local notation "C" => AlgebraicClosure K

variable [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers F))
  (v.adicCompletionIntegers F)]

/-- The union of the constructed stages is the fixed field of valuation inertia. -/
theorem local_inertia_fixedField_eq_maximalUnramified :
    IntermediateField.fixedField (localInertiaGroup v) = maximalUnramified R K C := by
  let U := IntermediateField.fixedField (localInertiaGroup v)
  let : IsGalois K U := by
    rw [← InfiniteGalois.normal_iff_isGalois]
    change U.fixingSubgroup.Normal
    rw [InfiniteGalois.fixingSubgroup_fixedField
      (⟨localInertiaGroup v, localInertiaGroup_isClosed v⟩ : ClosedSubgroup Gal(C/K))]
    infer_instance
  apply le_antisymm
  · intro x hx
    let t : U := ⟨x, hx⟩
    let A := FiniteGaloisIntermediateField.adjoin K {t}
    let E := IntermediateField.lift A.toIntermediateField
    let e := IntermediateField.liftAlgEquiv A.toIntermediateField
    let : FiniteDimensional K E := e.toLinearEquiv.finiteDimensional
    let : Normal K E := Normal.of_algEquiv e
    let : IsGalois K E := ⟨⟩
    have hi : localInertiaGroup v ≤ E.fixingSubgroup := by
      intro σ hσ
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      exact (IntermediateField.lift_le A.toIntermediateField hy) ⟨σ, hσ⟩
    have hu := isUnramifiedStage_of_local_inertia_le v E hi
    apply hu.le_maximalUnramified R K C
    exact (IntermediateField.mem_lift t).mpr
      (FiniteGaloisIntermediateField.subset_adjoin K {t} (Set.mem_singleton t))
  · intro x hx σ
    obtain ⟨n, hn⟩ := (mem_maximalUnramified_iff R K C x).mp hx
    let E := unramifiedStage R K C n
    have hu := unramifiedStage_isUnramified R K C n
    let : FiniteDimensional K E := hu.1
    let : Normal K E := hu.normal
    let : IsGalois K E := ⟨⟩
    exact (hu.local_inertia_le_fixingSubgroup v E σ.property) ⟨x, hn⟩

/-- Restriction to the constructed union has precisely the existing local inertia kernel. -/
theorem unramifiedRestriction_ker_eq_localInertia :
    (unramifiedRestriction R K C).ker = localInertiaGroup v := by
  let := maximalUnramified_normal R K C
  change (AlgEquiv.restrictNormalHom (maximalUnramified R K C)).ker = _
  rw [IntermediateField.restrictNormalHom_ker,
    ← local_inertia_fixedField_eq_maximalUnramified v]
  exact InfiniteGalois.fixingSubgroup_fixedField
    (⟨localInertiaGroup v, localInertiaGroup_isClosed v⟩ : ClosedSubgroup Gal(C/K))

end LocalClassFieldTheory
