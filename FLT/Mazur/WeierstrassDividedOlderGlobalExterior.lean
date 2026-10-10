/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedExteriorIntersection
public import FLT.Mazur.WeierstrassDividedOlderGlobalTensorCharts
public import FLT.Mazur.TensorOpenExteriorIntersection

/-!
# Full preceding-exterior intersections in the retained global tensor atlas

The original preceding exterior and the precise older successive chart
retain their complete horizontal intersection in every later global model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S]
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "u" => WeierstrassSuccessiveX.coord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "f" => finiteStructure hπ data (j + 1 + r) hr
local notation "i" => olderPrecedingExterior hπ data j hj r hr
local notation "c" => olderSuccessiveChart hπ data j hj r hr
local notation "hc" => olderSuccessiveChart_structure hπ data j hj r hr
local notation "emb" => finiteLocalTensorEmbedding hπ data S (j + 1 + r) hr

/-- The whole preceding exterior coefficient pullback inside the later global model. -/
def olderGlobalExteriorTensorChart := TensorOpenExterior.inclusion S f i ≫ emb

instance olderGlobalExteriorTensorChart_isOpenImmersion :
    IsOpenImmersion (olderGlobalExteriorTensorChart hπ data S j hj r hr) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

omit [IsBezout R] in
/-- The retained integral intersection is exactly the entire original horizontal localization. -/
theorem olderPrecedingExterior_principal_preimage :
    c ⁻¹' Set.range i = Set.range
      (Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away u)))) := by
  rw [olderPrecedingExterior_preimage, previousToX_range_horizontal hπ data j hj]
  rfl

/-- The actual global tensor chart has exactly the full horizontal principal preimage. -/
theorem olderGlobalExteriorTensor_preimage :
    olderGlobalTensorChart hπ data S j hj r hr ⁻¹'
      Set.range (olderGlobalExteriorTensorChart hπ data S j hj r hr) =
        Set.range (PrincipalOpenTensor.inclusion S u) := by
  change (emb ∘ TensorOpenChart.chart f c hc) ⁻¹'
    Set.range (emb ∘ TensorOpenExterior.inclusion S f i) = _
  rw [Set.range_comp, Set.preimage_comp,
    Set.preimage_image_eq _ (emb).isOpenEmbedding.injective]
  exact TensorOpenExterior.principal_preimage S f i c hc u
    (olderPrecedingExterior_principal_preimage hπ data j hj r hr)

/-- The original full horizontal tensor localization maps canonically to the preceding exterior. -/
def olderGlobalHorizontalToExterior :=
  TensorOpenExterior.principalToExterior S f i c hc u
    (olderPrecedingExterior_principal_preimage hπ data j hj r hr)

/-- Both horizontal boundary maps retain their actual global inclusions. -/
@[reassoc] theorem olderGlobalHorizontalToExterior_comp :
    olderGlobalHorizontalToExterior hπ data S j hj r hr ≫
      olderGlobalExteriorTensorChart hπ data S j hj r hr =
        PrincipalOpenTensor.inclusion S u ≫ olderGlobalTensorChart hπ data S j hj r hr := by
  change _ ≫ TensorOpenExterior.inclusion S f i ≫ emb =
    PrincipalOpenTensor.inclusion S u ≫ TensorOpenChart.chart f c hc ≫ emb
  exact TensorOpenExterior.principalToExterior_comp_assoc S f i c hc u
    (olderPrecedingExterior_principal_preimage hπ data j hj r hr) emb

/-- The full horizontal tensor open is the actual global intersection at every retained stage. -/
theorem olderGlobalExteriorTensor_isPullback :
    IsPullback (olderGlobalHorizontalToExterior hπ data S j hj r hr)
      (PrincipalOpenTensor.inclusion S u) (olderGlobalExteriorTensorChart hπ data S j hj r hr)
      (olderGlobalTensorChart hπ data S j hj r hr) := by
  apply IsOpenImmersion.isPullback
  · exact (olderGlobalHorizontalToExterior_comp hπ data S j hj r hr).symm
  · exact TopologicalSpace.Opens.ext (olderGlobalExteriorTensor_preimage hπ data S j hj r hr)

end FLT.Mazur.WeierstrassDividedDepth
