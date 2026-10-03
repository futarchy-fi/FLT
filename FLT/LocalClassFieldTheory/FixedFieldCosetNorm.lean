/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.NormalFixedFieldNorm
public import Mathlib.FieldTheory.SeparableDegree

/-!
# Fixed-field norms without normality

Cosets of an arbitrary subgroup index the embeddings of its fixed field in
an algebraic closure. The embedding product gives the actual field norm.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsGalois K L] [FiniteDimensional K L] (H : Subgroup Gal(L/K))
  [Fintype (Gal(L/K) ⧸ H)]

local notation "E" => IntermediateField.fixedField H
local notation "C" => AlgebraicClosure L

/-- Restrict a coset representative to an embedding of the fixed field. -/
def fixedFieldCosetEmbedding (q : Gal(L/K) ⧸ H) : E →ₐ[K] C :=
  (IsScalarTower.toAlgHom K L C).comp (q.out.toAlgHom.comp (E).val)

omit [Fintype (Gal(L/K) ⧸ H)] [IsGalois K L] in
/-- Different cosets give different fixed-field embeddings. -/
theorem fixedFieldCosetEmbedding_injective :
    Function.Injective (fixedFieldCosetEmbedding K L H) := by
  intro q r h
  have he (x : E) : q.out (x : L) = r.out (x : L) := by
    apply (algebraMap L C).injective
    exact congrArg (fun f : E →ₐ[K] C => f x) h
  have hh : q.out⁻¹ * r.out ∈ H := by
    apply (show (E).fixingSubgroup ≤ H from
      le_of_eq (IntermediateField.fixingSubgroup_fixedField H))
    intro x
    change q.out.symm (r.out (x : L)) = (x : L)
    rw [← he, AlgEquiv.symm_apply_apply]
  have hq : (QuotientGroup.mk q.out : Gal(L/K) ⧸ H) = QuotientGroup.mk r.out :=
    QuotientGroup.eq.mpr hh
  simpa only [QuotientGroup.out_eq'] using hq

omit [Fintype (Gal(L/K) ⧸ H)] in
/-- Cosets exhaust the embeddings because their cardinality is the fixed-field degree. -/
theorem fixedFieldCosetEmbedding_bijective :
    Function.Bijective (fixedFieldCosetEmbedding K L H) := by
  classical
  let : Fintype (Gal(L/K) ⧸ H) := Fintype.ofFinite _
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨fixedFieldCosetEmbedding_injective K L H, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    ← Field.finSepDegree_eq_of_isAlgClosed K E C,
    Field.finSepDegree_eq_finrank_of_isSeparable,
    IntermediateField.finrank_eq_fixingSubgroup_index,
    IntermediateField.fixingSubgroup_fixedField]
  rfl

/-- The fixed-field norm is the coset product for an arbitrary subgroup. -/
theorem fixedField_coset_norm (x : E) :
    algebraMap K L (Algebra.norm K x) = ∏ q : Gal(L/K) ⧸ H, q.out (x : L) := by
  classical
  apply (algebraMap L C).injective
  rw [← IsScalarTower.algebraMap_apply, Algebra.norm_eq_prod_embeddings, map_prod]
  let e := Equiv.ofBijective (fixedFieldCosetEmbedding K L H)
    (fixedFieldCosetEmbedding_bijective K L H)
  exact (e.prod_comp (fun f : E →ₐ[K] C => f x)).symm

/-- The transfer on fixed units is the norm without a normality assumption. -/
theorem transferInvariant_fixedField_coset_norm (v : Eˣ) :
    transferInvariant (Rep.ofAlgebraAutOnUnits K L) H
      (fixedUnitInvariantInclusion K L H (Additive.ofMul v)) =
      finiteUnitInvariantInclusion K L (Additive.ofMul (Units.map (Algebra.norm K) v)) := by
  classical
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Units.ext
  change ((Additive.toMul (transferZero (Rep.ofAlgebraAutOnUnits K L) H _)) : Lˣ).val =
    algebraMap K L (Algebra.norm K (v : E))
  rw [transferZero_apply, toMul_sum, Units.coe_prod]
  exact (fixedField_coset_norm K L H (v : E)).symm

end LocalClassFieldTheory
