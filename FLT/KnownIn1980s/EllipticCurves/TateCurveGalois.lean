/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurve
public import FLT.TateCurve.AlgebraicPointLocal
public import FLT.TateCurve.ModelGalois

/-!
# Galois compatibility of the chosen Tate uniformization

The local uniformization uses an isomorphism chosen over the extension field.
Split multiplicative reduction forces that isomorphism to be Galois-fixed.
-/

@[expose] public section

open ValuativeRel
open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (E : WeierstrassCurve K) [E.IsElliptic] [E.HasSplitMultiplicativeReduction 𝒪[K]]

variable [DecidableEq K] in
/-- On representatives, the chosen uniformization is the local coordinate map followed by
the inverse change of Weierstrass coordinates. -/
theorem tateEquiv_apply_eq_local (u : Kˣ) :
    E.tateEquiv (Additive.ofMul ↑u) =
      Affine.Point.equivOfEq E.exists_variableChange_tateCurve.choose_spec
        ((Affine.Point.equivVariableChange (tateCurve E.q)
          E.exists_variableChange_tateCurve.choose).symm
          (TateCurve.uniformizationPoint E.qUnit E.valuation_q_lt_one u)) := by
  let : ValuativeExtension K K := ⟨fun _ _ ↦ Iff.rfl⟩
  change E.tateModelEquiv K
    (TateCurve.FiniteStages.algebraicPoint E.qUnit E.valuation_q_lt_one u) = _
  rw [TateCurve.FiniteStages.algebraicPoint_eq_uniformizationPointOver
    E.qUnit E.valuation_q_lt_one continuous_id]
  rfl

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- The extension-field choice of Tate-model isomorphism is fixed by base-linear automorphisms. -/
theorem tateModel_variableChange_galois (σ : L ≃ₐ[K] L) :
    (E.baseChange L).exists_variableChange_tateCurve.choose.map σ.toAlgHom.toRingHom =
      (E.baseChange L).exists_variableChange_tateCurve.choose := by
  let : (tateCurve E.q).HasSplitMultiplicativeReduction 𝒪[K] :=
    TateCurve.tateCurve_hasSplitMultiplicativeReduction E.q_ne_zero E.valuation_q_lt_one
  apply map_variableChange_eq_of_hasSplitMultiplicativeReduction (tateCurve E.q) E L
  have hq : (tateCurve E.q).baseChange L = tateCurve (E.baseChange L).q := by
    rw [E.q_baseChange]
    exact tateCurve_baseChange E.q E.valuation_q_lt_one
  rw [hq]
  exact (E.baseChange L).exists_variableChange_tateCurve.choose_spec

end WeierstrassCurve
