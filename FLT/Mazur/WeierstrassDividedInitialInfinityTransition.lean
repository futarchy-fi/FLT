/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialTensorInfinityIntersection
public import FLT.Mazur.WeierstrassModificationXInitialInfinityTensor

/-!
# The actual finite-model infinity attachment is the original tensor transition

The global original y-boundary map and the explicit projective transition
agree on both coefficient and integral-curve projections. This identifies the
entire map at every finite stage, before any residue normalization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j ≤ n)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "y" => WeierstrassModificationX.y W (π ^ start) (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => initialGlobalYToInfinity hπ data S j hj
local notation "f" => initialInfinityTensorTransition W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) S

/-- The full original infinity attachment retains the coefficient structure. -/
@[reassoc] theorem initialGlobalYToInfinity_structure :
    t ≫ Spec.map (CommRingCat.ofHom
      (algebraMap S (S ⊗[R] WeierstrassIntegralChart.Coordinate W 1))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap S (Localization.Away ((1 : S) ⊗ₜ[R] y)))) := by
  rw [← finiteInfinityTensorChart_structure hπ data S j hj,
    initialGlobalYToInfinity_comp_assoc, globalInitialTensorChart_structure,
    PrincipalOpenTensor.inclusion_structure]

/-- The original finite-model transition has the full original integral infinity projection. -/
@[reassoc] theorem initialGlobalYToInfinity_projection :
    t ≫ TensorOpenChart.projection =
      Spec.map (CommRingCat.ofHom (f).toRingHom) ≫ TensorOpenChart.projection := by
  apply (cancel_mono (integralCurveChart W 1)).mp
  rw [Category.assoc, Category.assoc, initialInfinityTensorTransition_toCurve]
  rw [← finiteInfinityTensorChart_toCurve hπ data S j hj,
    initialGlobalYToInfinity_comp_assoc, globalInitialTensorChart_toCurve]

/-- The actual finite-model attachment is exactly the tensor of the original projective map. -/
theorem initialGlobalYToInfinity_eq_spec :
    t = Spec.map (CommRingCat.ofHom (f).toRingHom) := by
  apply (cancel_mono (pullbackSpecIso R S (WeierstrassIntegralChart.Coordinate W 1)).inv).mp
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSpecIso_inv_fst']
    rw [initialGlobalYToInfinity_structure, ← Spec.map_comp]
    apply congrArg Spec.map
    exact CommRingCat.hom_ext (RingHom.ext (fun a => ((f).commutes a).symm))
  · simp only [Category.assoc, pullbackSpecIso_inv_snd]
    exact initialGlobalYToInfinity_projection hπ data S j hj

end FLT.Mazur.WeierstrassDividedDepth
