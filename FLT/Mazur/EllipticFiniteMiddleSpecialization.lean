/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteDividedSpecialization
public import FLT.Mazur.WeierstrassDividedTerminalResidueCharts
public import FLT.Mazur.PolygonAtlasSmoothLocus
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Smooth specialization of original points at the even middle depth

Primitive coordinates at the final even divided depth give a point of the
actual terminal Laurent chart. Its inclusion is exactly the unrestricted
proper specialization, hence these nonidentity points specialize smoothly.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j) ≤ depth)
  (hm : 2 * (start + j) = depth)
  (P : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = start + j)
local notation "k" => ResidueField A
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
local notation "C" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A k))
local notation "f" => finiteGlobalStructure hπ data j hj
local notation "p" => pullback.fst q f
local notation "e" => WeierstrassDilatation.residueLaurentIso D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hm
local notation "c" => terminalLaurentChart hπ data D j hj hk0 hk hm

/-- The actual Laurent coordinates of an original point at final even depth. -/
def finiteMiddleLaurentPoint : Spec (.of k) ⟶ Spec (.of k[T;T⁻¹]) :=
  Spec.map (CommRingCat.ofHom (AlgHom.liftEquiv A k C k
    (finiteNodeCoefficientEvaluation A hπ data j hj P v hv k)).toRingHom) ≫ (e).inv

/-- Laurent reconstruction recovers the original point's actual proper closed specialization. -/
@[reassoc] theorem finiteMiddleLaurentPoint_inclusion :
    finiteMiddleLaurentPoint A hπ data D j hj hk0 hk hm P v hv ≫ c =
      finitePointSpecialization A hπ data j hj P := by
  rw [finiteMiddleLaurentPoint, terminalLaurentChart, Category.assoc, Iso.inv_hom_id_assoc]
  exact finitePointSpecialization_nodeChart A hπ data j hj P v hv

/-- The Laurent point is rational over the original residue field. -/
@[reassoc] theorem finiteMiddleLaurentPoint_structure :
    finiteMiddleLaurentPoint A hπ data D j hj hk0 hk hm P v hv ≫
      (MultiplicativeGroupScheme.gm k).hom = 𝟙 _ := by
  rw [← terminalLaurentChart_structure hπ data D j hj hk0 hk hm,
    ← Category.assoc, finiteMiddleLaurentPoint_inclusion]
  exact finitePointSpecialization_structure A hπ data j hj P

/-- The actual closed finite model is locally of finite presentation over its residue field. -/
theorem finitePointSpecializationStructure_lfp : LocallyOfFinitePresentation p := by
  infer_instance

include D hk0 hk hm v hv in
/-- At the even middle depth the unrestricted original specialization is actually smooth. -/
theorem finitePointSpecialization_middle_smooth (x : Spec (.of k)) :
    let _ := finitePointSpecializationStructure_lfp A hπ data j hj
    finitePointSpecialization A hπ data j hj P x ∈ (p).smoothLocus := by
  let _ := finitePointSpecializationStructure_lfp A hπ data j hj
  rw [← finiteMiddleLaurentPoint_inclusion A hπ data D j hj hk0 hk hm P v hv]
  apply (PolygonAtlas.mem_smooth_iff c p _).mpr
  have hc : Smooth (c ≫ p) := by
    rw [terminalLaurentChart_structure]
    exact MultiplicativeGroupScheme.smooth k
  let _ := hc
  rw [Scheme.Hom.smoothLocus_eq_top]
  trivial

end FLT.Mazur.WeierstrassDividedDepth
