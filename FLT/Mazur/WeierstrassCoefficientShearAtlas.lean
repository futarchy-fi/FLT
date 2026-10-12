/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearCoverage

/-!
# A complete open atlas of actual sheared coefficient equations

The three distinguished charts are infinity, divided, and initial incidence.
The remaining charts are the full successive equations indexed by their birth depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (t : ℕ) (ht : t ≤ n)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "q" => algebraMap R S
local notation "d" => data (Fin.mk t (Nat.lt_succ_of_le ht))
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))

omit hπ in
/-- Actual full affine equations of the complete coefficient shear atlas. -/
def coefficientShearAtlasObject : Fin 3 ⊕ Fin t → Scheme :=
  Sum.elim
    (Fin.cases (Spec (.of (S ⊗[R] WeierstrassIntegralChart.Coordinate W 1)))
      (Fin.cases
        (Spec (.of (WeierstrassDilatation.Coordinate U (q (π ^ (start + t)))
          (q (Data.b3 d)) (q (Data.b4 d) - r * q (Data.b3 d)) (q (Data.b6 d)))))
        (fun _ => Spec (.of (WeierstrassModificationX.Coordinate U (q (π ^ start))
          (q (Data.b3 d₀)) (q (Data.b4 d₀) - r * q (Data.b3 d₀)) (q (Data.b6 d₀)))))))
    (fun j => let e := data (Fin.mk (j.val + 1) (by omega))
      Spec (.of (WeierstrassSuccessiveX.Coordinate U (q (π ^ (start + j.val))) (q π)
        (q (Data.b3 e)) (q (Data.b4 e) - r * q (Data.b3 e)) (q (Data.b6 e)))))

/-- The original full chart embeddings, with all retained stages at the same final depth. -/
def coefficientShearAtlasMap (i : Fin 3 ⊕ Fin t) :
    coefficientShearAtlasObject data S r t ht i ⟶ finiteGlobalTensorModel hπ data S t ht :=
  match i with
  | .inl i => Fin.cases (finiteInfinityTensorChart hπ data S t ht)
      (Fin.cases (globalDividedCoefficientShearChart hπ data S r t ht)
        (fun _ => globalInitialCoefficientShearChart hπ data S r t ht)) i
  | .inr j => retainedCoefficientShearChart hπ data S r t ht j.val (by omega)

instance coefficientShearAtlasMap_isOpenImmersion (i : Fin 3 ⊕ Fin t) :
    IsOpenImmersion (coefficientShearAtlasMap hπ data S r t ht i) := by
  rcases i with i | j
  · fin_cases i
    · exact finiteInfinityTensorChart_isOpenImmersion hπ data S t ht
    · exact globalDividedCoefficientShearChart_isOpenImmersion hπ data S r t ht
    · exact globalInitialCoefficientShearChart_isOpenImmersion hπ data S r t ht
  · exact retainedCoefficientShearChart_isOpenImmersion hπ data S r t ht j.val (by omega)

/-- The actual full equation atlas covers every point, including at depth zero. -/
theorem coefficientShearAtlas_cover (z : finiteGlobalTensorModel hπ data S t ht) :
    ∃ i x, coefficientShearAtlasMap hπ data S r t ht i x = z := by
  rcases coefficientShearCharts_cover hπ data S r t ht z with h | h | h | ⟨j, h⟩
  · obtain ⟨x, hx⟩ := h
    exact ⟨.inl 0, x, hx⟩
  · obtain ⟨x, hx⟩ := h
    exact ⟨.inl 1, x, hx⟩
  · obtain ⟨x, hx⟩ := h
    exact ⟨.inl 2, x, hx⟩
  · obtain ⟨x, hx⟩ := h
    exact ⟨.inr j, x, hx⟩

/-- The complete sheared equations form an open cover of the original global pullback. -/
def coefficientShearOpenCover : (finiteGlobalTensorModel hπ data S t ht).OpenCover where
  I₀ := Fin 3 ⊕ Fin t
  X := coefficientShearAtlasObject data S r t ht
  f := coefficientShearAtlasMap hπ data S r t ht
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨coefficientShearAtlas_cover hπ data S r t ht,
      fun i => coefficientShearAtlasMap_isOpenImmersion hπ data S r t ht i⟩

end FLT.Mazur.WeierstrassDividedDepth
