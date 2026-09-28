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

/-- The chosen extension-field isomorphism has the base-changed Tate model as source. -/
theorem tateModel_smul_baseChange :
    (E.baseChange L).exists_variableChange_tateCurve.choose •
      (tateCurve E.q).baseChange L = E.baseChange L := by
  have hq : (tateCurve E.q).baseChange L = tateCurve (E.baseChange L).q := by
    rw [E.q_baseChange]
    exact tateCurve_baseChange E.q E.valuation_q_lt_one
  rw [hq]
  exact (E.baseChange L).exists_variableChange_tateCurve.choose_spec

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

variable [DecidableEq L]

/-- The local uniformization over the extension uses its chosen model isomorphism and
the base-field Tate series. -/
theorem tateEquiv_baseChange_apply_eq_local (u : Lˣ) :
    (E.baseChange L).tateEquiv (Additive.ofMul ↑u) =
      Affine.Point.equivOfEq E.tateModel_smul_baseChange
        ((Affine.Point.equivVariableChange ((tateCurve E.q).baseChange L)
          (E.baseChange L).exists_variableChange_tateCurve.choose).symm
          (TateCurve.uniformizationPointOver L E.qUnit E.valuation_q_lt_one u)) := by
  let : ((tateCurve E.q).baseChange L).IsElliptic :=
    inferInstanceAs ((tateCurve E.q).map (algebraMap K L)).IsElliptic
  rw [tateEquiv_apply_eq_local]
  have hq : tateCurve (E.baseChange L).q = (tateCurve E.q).baseChange L := by
    rw [E.q_baseChange]
    exact (tateCurve_baseChange E.q E.valuation_q_lt_one).symm
  erw [Affine.Point.equivVariableChange_symm_congr _ hq _ E.tateModel_smul_baseChange]
  apply congrArg (Affine.Point.equivOfEq E.tateModel_smul_baseChange)
  apply congrArg ((Affine.Point.equivVariableChange ((tateCurve E.q).baseChange L)
    (E.baseChange L).exists_variableChange_tateCurve.choose).symm)
  have huq : (E.baseChange L).qUnit = Units.map (algebraMap K L).toMonoidHom E.qUnit := by
    ext
    exact E.q_baseChange
  unfold TateCurve.uniformizationPointOver
  have transport : ∀ (q q' : Lˣ) (hq : valuation L (q : L) < 1)
      (hq' : valuation L (q' : L) < 1) (heq : q = q') (W : WeierstrassCurve L)
      (hW : tateCurve (q : L) = W) (hW' : tateCurve (q' : L) = W),
      Affine.Point.equivOfEq hW (TateCurve.uniformizationPoint q hq u) =
        Affine.Point.equivOfEq hW' (TateCurve.uniformizationPoint q' hq' u) := by
    intro q q' hq hq' heq W hW hW'
    subst q'
    rfl
  exact transport _ _ _ _ huq _ _ _

/-- The chosen local Tate uniformization commutes with every continuous base-linear
automorphism, even though its model isomorphism is chosen over the extension. -/
theorem tateEquiv_galois_proved (σ : L ≃ₐ[K] L) (hσ : Continuous σ) (u : Lˣ) :
    Affine.Point.map (W' := E) σ.toAlgHom
        ((E.baseChange L).tateEquiv (Additive.ofMul ↑u) : (E⁄L).Point) =
      (E.baseChange L).tateEquiv
        (Additive.ofMul ↑(Units.map σ.toAlgHom.toRingHom.toMonoidHom u)) := by
  let : ((tateCurve E.q).baseChange L).IsElliptic :=
    inferInstanceAs ((tateCurve E.q).map (algebraMap K L)).IsElliptic
  rw [E.tateEquiv_baseChange_apply_eq_local, E.tateEquiv_baseChange_apply_eq_local]
  erw [Affine.Point.map_modelEquiv_of_fixed (tateCurve E.q) E _ _ σ
      (E.tateModel_variableChange_galois σ)]
  apply congrArg (Affine.Point.equivOfEq E.tateModel_smul_baseChange)
  apply congrArg ((Affine.Point.equivVariableChange ((tateCurve E.q).baseChange L)
    (E.baseChange L).exists_variableChange_tateCurve.choose).symm)
  exact TateCurve.uniformizationPointOver_galois σ hσ E.qUnit E.valuation_q_lt_one u

end WeierstrassCurve
