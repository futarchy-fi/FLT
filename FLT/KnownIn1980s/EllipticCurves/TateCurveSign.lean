/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurveGalois
public import FLT.TateCurve.ModelSign
public import FLT.TateCurve.ValuativeContinuity

/-!
# Base change of the chosen Tate uniformization

The coordinate series commute with a valuative embedding. Comparing the two
chosen model isomorphisms leaves precisely one uniform sign.
-/

@[expose] public section

open ValuativeRel
open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.Point

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [DecidableEq L]

/-- Model transport over an extension is transport by the mapped coordinate change. -/
theorem modelEquivOver_eq (V W : WeierstrassCurve K) [V.IsElliptic]
    (C : VariableChange K) (hC : C • V = W)
    (hL : C.map (algebraMap K L) • V.baseChange L = W.baseChange L)
    (P : (V⁄L).Point) :
    modelEquivOver V W C hC P =
      equivOfEq hL ((equivVariableChange (V.baseChange L) (C.map (algebraMap K L))).symm P) := by
  let : (V.baseChange L).IsElliptic := inferInstanceAs (V.map (algebraMap K L)).IsElliptic
  have transport : ∀ {A B D : WeierstrassCurve L} (h : A = B) (h' : A = D)
      (h'' : B = D) (Q : B.toAffine.Point),
      equivOfEq h' ((equivOfEq h).symm Q) = equivOfEq h'' Q := by
    intro A B D h h' h'' Q
    subst B
    subst D
    rfl
  unfold modelEquivOver equivVariableChangeOver
  exact transport _ _ _ _

end WeierstrassCurve.Affine.Point

namespace WeierstrassCurve

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (E : WeierstrassCurve K) [E.IsElliptic] [E.HasSplitMultiplicativeReduction 𝒪[K]]
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [DecidableEq K] [DecidableEq L]

/-- Transporting the base-field uniformization gives the same convergent Tate point
over the extension, using the base-field model isomorphism. -/
theorem baseChange_tateEquiv_eq_local (u : Kˣ) :
    Affine.Point.baseChange (W' := E) K L (E.tateEquiv (Additive.ofMul ↑u)) =
      E.tateModelEquiv L
        (TateCurve.uniformizationPointOver L E.qUnit E.valuation_q_lt_one
          (Units.map (algebraMap K L).toMonoidHom u)) := by
  let : ValuativeExtension K K := ⟨fun _ _ ↦ Iff.rfl⟩
  change Affine.Point.map (Algebra.ofId K L)
    (E.tateModelEquiv K (TateCurve.FiniteStages.algebraicPoint E.qUnit E.valuation_q_lt_one u)) = _
  rw [TateCurve.FiniteStages.algebraicPoint_eq_uniformizationPointOver
    E.qUnit E.valuation_q_lt_one continuous_id]
  unfold tateModelEquiv
  erw [Affine.Point.map_modelEquivOver]
  apply congrArg (E.tateModelEquiv L)
  exact TateCurve.map_uniformizationPointOver (Algebra.ofId K L)
    (TateCurve.continuous_algebraMap_of_valuation_lt_one E.q_ne_zero E.valuation_q_lt_one)
    E.qUnit E.valuation_q_lt_one u

/-- The two chosen Tate uniformizations commute with base change up to a uniform sign. -/
theorem tateEquiv_baseChange_proved :
    ∃ ε : ℤˣ, ∀ u : Kˣ,
      Affine.Point.baseChange (W' := E) K L (E.tateEquiv (Additive.ofMul ↑u)) =
        (ε : ℤ) • (E.baseChange L).tateEquiv
          (Additive.ofMul
            (Units.map (algebraMap K L).toMonoidHom u :
              Lˣ ⧸ Subgroup.zpowers (E.baseChange L).qUnit)) := by
  let V := (tateCurve E.q).baseChange L
  let C := E.exists_variableChange_tateCurve.choose.map (algebraMap K L)
  let D := (E.baseChange L).exists_variableChange_tateCurve.choose
  have hC : C • V = E.baseChange L := by
    change C • (tateCurve E.q).map (algebraMap K L) = E.baseChange L
    rw [map_variableChange]
    exact congrArg (fun W : WeierstrassCurve K ↦ W.baseChange L)
      E.exists_variableChange_tateCurve.choose_spec
  have hD : D • V = E.baseChange L := E.tateModel_smul_baseChange
  let : (tateCurve E.q).HasSplitMultiplicativeReduction 𝒪[K] :=
    TateCurve.tateCurve_hasSplitMultiplicativeReduction E.q_ne_zero E.valuation_q_lt_one
  have h4 : V.c₄ ≠ 0 := by
    change ((tateCurve E.q).map (algebraMap K L)).c₄ ≠ 0
    rw [map_c₄]
    exact (map_ne_zero _).mpr (tateCurve E.q).c₄_ne_zero_of_hasMultiplicativeReduction
  have h6 : V.c₆ ≠ 0 := by
    change ((tateCurve E.q).map (algebraMap K L)).c₆ ≠ 0
    rw [map_c₆]
    exact (map_ne_zero _).mpr (tateCurve E.q).c₆_ne_zero_of_hasMultiplicativeReduction
  obtain ⟨ε, hε⟩ := Affine.Point.exists_sign_modelEquiv V (E.baseChange L) h4 h6 C D hC hD
  refine ⟨ε, fun u ↦ ?_⟩
  rw [E.baseChange_tateEquiv_eq_local, E.tateEquiv_baseChange_apply_eq_local]
  unfold tateModelEquiv
  erw [Affine.Point.modelEquivOver_eq _ _ _ _ hC]
  exact hε _

end WeierstrassCurve
