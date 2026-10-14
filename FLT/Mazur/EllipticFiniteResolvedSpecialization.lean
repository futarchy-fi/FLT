/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteRetainedSmoothSpecialization
public import FLT.Mazur.EllipticFiniteOddSpecialization
public import FLT.Mazur.WeierstrassDividedSmoothCoefficientEmbedding

/-!
# Every original point specializes smoothly on the fully divided split model

Original smooth points lie in the retained original smooth open. Every other
point has positive primitive depth: shallower depths use retained horizontal
charts, and the final depth uses the even Laurent or odd punctured node chart.
All cases refer to the same unrestricted proper specialization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0)

/-- Original smooth reduction gives smooth specialization in every finite modified model. -/
theorem finitePointSpecialization_e0_smooth {start n : ℕ}
    (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : SmoothReduction A W P)
    (x : Spec (.of (ResidueField A))) :
    let _ := finitePointSpecializationStructure_lfp A hπ data j hj
    finitePointSpecialization A hπ data j hj P x ∈
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A (ResidueField A))))
        (finiteGlobalStructure hπ data j hj)).smoothLocus := by
  let _ := finitePointSpecializationStructure_lfp A hπ data j hj
  let emb := finiteGlobalSmoothCoefficientEmbedding (ResidueField A) hπ data j hj
  have hx : finitePointSpecialization A hπ data j hj P x ∈ Set.range emb := by
    rw [finiteGlobalSmoothCoefficientEmbedding_range]
    change (finitePointSpecialization A hπ data j hj P ≫ pullback.snd _ _) x ∈
      Set.range (finiteGlobalSmoothEmbedding hπ data j hj)
    have hproj : finitePointSpecialization A hπ data j hj P ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A (ResidueField A))))
          (finiteGlobalStructure hπ data j hj) =
        Spec.map (CommRingCat.ofHom (residue A)) ≫ finitePointSection A hπ data j hj P :=
      finitePointSpecialization_projection A hπ data j hj P
    rw [hproj, finitePointSection_e0 A hπ data j hj ⟨P, hP⟩]
    exact ⟨_, rfl⟩
  obtain ⟨y, hy⟩ := hx
  rw [← hy]
  apply (PolygonAtlas.mem_smooth_iff emb _ y).mpr
  have hs : Smooth (emb ≫ pullback.fst _ _) := by
    rw [finiteGlobalSmoothCoefficientEmbedding_structure]
    infer_instance
  let _ := hs
  rw [Scheme.Hom.smoothLocus_eq_top]
  trivial

/-- Reindex the retained specialization theorem by any later stage of the same finite model. -/
theorem finitePointSpecialization_retained_smooth_of_lt {start n depth : ℕ}
    (data : (i : Fin (n + 1)) → Data W π (start + i.val))
    (D : SplitNodeDepth W π depth) (j m : ℕ) (hm : m ≤ n) (hjm : j < m)
    (hk0 : 0 < start + j) (hp : 2 * (start + j) < depth)
    (P : (W.map (algebraMap A K)).toProjective.Point)
    (v : NodePointCoordinates A W π P) (hv : v.depth = start + j)
    (x : Spec (.of (ResidueField A))) :
    let _ := finitePointSpecializationStructure_lfp A hπ data m hm
    finitePointSpecialization A hπ data m hm P x ∈
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A (ResidueField A))))
        (finiteGlobalStructure hπ data m hm)).smoothLocus := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hjm
  exact finitePointSpecialization_retained_smooth A hπ data D j (by omega) r hm hk0
    (by omega) hp P v hv x

variable {depth : ℕ} (D : SplitNodeDepth W π depth)
  (data : (i : Fin (depth / 2 + 1)) → Data W π (0 + i.val))

include D in
/-- At the final divided stage every original point has actual smooth closed specialization. -/
theorem finitePointSpecialization_resolved_smooth
    (P : (W.map (algebraMap A K)).toProjective.Point) (x : Spec (.of (ResidueField A))) :
    let _ := finitePointSpecializationStructure_lfp A hπ data (depth / 2) (le_refl _)
    finitePointSpecialization A hπ data (depth / 2) (le_refl _) P x ∈
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A (ResidueField A))))
        (finiteGlobalStructure hπ data (depth / 2) (le_refl _))).smoothLocus := by
  by_cases hP : SmoothReduction A W P
  · exact finitePointSpecialization_e0_smooth A hπ data (depth / 2) (le_refl _) P hP x
  obtain ⟨v, hv⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq depth
    D.a₃_mem D.a₄_mem D.a₆_not_mem P hP
  have hπm : π ∈ maximalIdeal A := D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have h3 : W.a₃ ∈ maximalIdeal A := Ideal.pow_le_self (by omega) D.a₃_mem
  have h4 : W.a₄ ∈ maximalIdeal A := Ideal.pow_le_self (by omega) D.a₄_mem
  have h6 : W.a₆ ∈ maximalIdeal A := Ideal.pow_le_self (by have := D.depth_pos; omega) D.a₆_mem
  have hk0 : 0 < v.depth := by
    by_contra hn
    exact hP ((v.smooth_iff hπm h3 h4 h6).mpr (by omega))
  by_cases he : v.depth = depth / 2
  · have hk : 2 * (0 + depth / 2) ≤ depth := by omega
    by_cases hm : 2 * (0 + depth / 2) = depth
    · exact finitePointSpecialization_middle_smooth A hπ data D (depth / 2) (le_refl _)
        (by omega) hk hm P v (by omega) x
    · exact finitePointSpecialization_odd_smooth A hπ data D (depth / 2) (le_refl _)
        (by omega) hk (by omega) (by omega) P v (by omega) x
  · exact finitePointSpecialization_retained_smooth_of_lt A hπ data D v.depth
      (depth / 2) (le_refl _) (by omega) (by omega) (by omega) P v (by omega) x

end FLT.Mazur.WeierstrassDividedDepth
