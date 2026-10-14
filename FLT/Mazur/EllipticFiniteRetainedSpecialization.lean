/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteRetainedNodeSection
public import FLT.Mazur.EllipticFiniteCoefficientPointSection

/-!
# Actual coefficient specialization of retained primitive sections

The original horizontal localization gives a tensor chart in every later
finite model. Its coefficient evaluation is the unrestricted proper section
with those coefficients, including the actual closed specialization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "B" => WeierstrassDilatation.HorizontalCoordinate W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "c" => finiteRetainedBoundaryChart A hπ data j hj r hr
local notation "f" => finiteGlobalStructure hπ data (j + 1 + r) hr

/-- The retained boundary structure is exactly the original algebra structure. -/
@[reassoc] theorem finiteRetainedBoundaryChart_algebra :
    c ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
  rw [finiteRetainedBoundaryChart_structure]
  rw [show toCurve d ≫ WeierstrassIntegralChart.integralCurveStructure W =
    Spec.map (CommRingCat.ofHom (algebraMap A
      (WeierstrassDilatation.Coordinate W (π ^ (start + j))
        (Data.b3 d) (Data.b4 d) (Data.b6 d)))) from
          WeierstrassDilatation.toCurve_structure ..]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1

variable (S : Type u) [CommRing S] [Algebra A S]
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A S))

/-- The actual horizontal tensor open retained in the later coefficient model. -/
def finiteRetainedBoundaryTensorChart : Spec (.of (S ⊗[A] B)) ⟶
    finiteGlobalTensorModel hπ data S (j + 1 + r) hr :=
  TensorOpenChart.chart f c (finiteRetainedBoundaryChart_algebra A hπ data j hj r hr)

instance finiteRetainedBoundaryTensorChart_isOpenImmersion :
    IsOpenImmersion (finiteRetainedBoundaryTensorChart A hπ data j hj r hr S) :=
  inferInstanceAs (IsOpenImmersion (TensorOpenChart.chart _ _ _))

/-- The retained tensor chart has its actual coefficient projection. -/
@[reassoc] theorem finiteRetainedBoundaryTensorChart_structure :
    finiteRetainedBoundaryTensorChart A hπ data j hj r hr S ≫ pullback.fst q f =
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[A] B))) :=
  TensorOpenChart.chart_fst _ _ _

variable {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hk0 : 0 < start + j) (hp : 2 * (start + j) < depth)
  (P : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = start + j)
local notation "b" => finiteNodeBoundaryEvaluation A hπ data D j
  (Nat.le_of_succ_le hj) hk0 hp P v hv
local notation "g" => AlgHom.liftEquiv A S B S (AlgHom.comp (IsScalarTower.toAlgHom A A S) b)

/-- The original retained coordinates compute the actual coefficient specialization. -/
theorem finiteCoefficientPointSection_retainedChart :
    Spec.map (CommRingCat.ofHom (g).toRingHom) ≫
      finiteRetainedBoundaryTensorChart A hπ data j hj r hr S =
        finiteCoefficientPointSection A hπ data (j + 1 + r) hr S P := by
  apply pullback.hom_ext
  · rw [Category.assoc, finiteRetainedBoundaryTensorChart_structure,
      finiteCoefficientPointSection_structure, ← Spec.map_comp]
    have he : CommRingCat.ofHom (algebraMap S (S ⊗[A] B)) ≫
        CommRingCat.ofHom (g).toRingHom = 𝟙 (CommRingCat.of S) := by
      ext s
      exact (g).commutes s
    rw [he, Spec.map_id]
  · rw [Category.assoc, finiteCoefficientPointSection_projection]
    change Spec.map _ ≫ TensorOpenChart.chart _ _ _ ≫ _ = _
    rw [TensorOpenChart.chart_snd, ← Category.assoc]
    have he : Spec.map (CommRingCat.ofHom (g).toRingHom) ≫ TensorOpenChart.projection =
        q ≫ Spec.map (CommRingCat.ofHom (b).toRingHom) := by
      rw [TensorOpenChart.projection, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      exact (AlgHom.liftEquiv_tmul _ (1 : S) z).trans (one_smul S _)
    rw [he, Category.assoc]
    change q ≫ finiteRetainedNodeSection A hπ data j hj r hr D hk0 hp P v hv = _
    rw [finiteRetainedNodeSection_eq]

include D hk0 hp v hv in
/-- Every actual coefficient point lies in the retained horizontal tensor open. -/
theorem finiteCoefficientPointSection_mem_retainedChart (z : Spec (.of S)) :
    finiteCoefficientPointSection A hπ data (j + 1 + r) hr S P z ∈
      Set.range (finiteRetainedBoundaryTensorChart A hπ data j hj r hr S) := by
  rw [← finiteCoefficientPointSection_retainedChart A hπ data j hj r hr S D hk0 hp P v hv]
  exact ⟨_, rfl⟩

end FLT.Mazur.WeierstrassDividedDepth
