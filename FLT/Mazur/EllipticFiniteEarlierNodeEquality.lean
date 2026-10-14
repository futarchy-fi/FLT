/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteEarlierNodeSection
public import FLT.Mazur.EllipticFiniteSpecializationEqualityDescent

/-!
# Earlier divided residues distinguish actual specializations

Project equality to the original finite model and cancel its divided open
immersion. Faithfulness of the affine spectrum then recovers equality of
both scaled divided residues, even when the primitive depths differ.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (P Q : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : start + j ≤ v.depth)
  (w : NodePointCoordinates A W π Q) (hw : start + j ≤ w.depth)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
local notation "q" => Spec.map (CommRingCat.ofHom (residue A))
local notation "f" => finiteGlobalStructure hπ data j hj

include hv hw in
/-- Equal actual specializations have equal earlier divided residues. -/
theorem finitePointSpecialization_earlier_residues
    (he : finitePointSpecialization A hπ data j hj P =
      finitePointSpecialization A hπ data j hj Q) :
    residue A (π ^ (v.depth - (start + j)) * v.a) =
        residue A (π ^ (w.depth - (start + j)) * w.a) ∧
      residue A (π ^ (v.depth - (start + j)) * v.b) =
        residue A (π ^ (w.depth - (start + j)) * w.b) := by
  let _ : IsOpenImmersion (finiteDividedGlobalChart hπ data j hj) := by
    unfold finiteDividedGlobalChart
    infer_instance
  have e := congrArg (· ≫ pullback.snd q f) he
  rw [finitePointSpecialization_projection, finitePointSpecialization_projection,
    ← finitePointSection_earlierNodeChart A hπ data j hj P v hv,
    ← finitePointSection_earlierNodeChart A hπ data j hj Q w hw,
    ← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at e
  have eh := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  constructor
  · have ex := congrArg (fun g => g (WeierstrassDilatation.x W (π ^ (start + j))
      (Data.b3 d) (Data.b4 d) (Data.b6 d))) eh
    change residue A ((finiteEarlierNodeEvaluation A hπ data j hj P v hv) _) =
      residue A ((finiteEarlierNodeEvaluation A hπ data j hj Q w hw) _) at ex
    simpa only [finiteEarlierNodeEvaluation, WeierstrassDilatation.evaluation_x] using ex
  · have ey := congrArg (fun g => g (WeierstrassDilatation.y W (π ^ (start + j))
      (Data.b3 d) (Data.b4 d) (Data.b6 d))) eh
    change residue A ((finiteEarlierNodeEvaluation A hπ data j hj P v hv) _) =
      residue A ((finiteEarlierNodeEvaluation A hπ data j hj Q w hw) _) at ey
    simpa only [finiteEarlierNodeEvaluation, WeierstrassDilatation.evaluation_y] using ey

/-- Resolved equality recovers both earlier coordinate residues at every common stage. -/
theorem resolvedSplitSmoothPoint_earlier_residues {depth : ℕ}
    (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ depth / 2)
    (v : NodePointCoordinates A W π P) (hv : j ≤ v.depth)
    (w : NodePointCoordinates A W π Q) (hw : j ≤ w.depth)
    (he : resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q) :
    residue A (π ^ (v.depth - j) * v.a) = residue A (π ^ (w.depth - j) * w.a) ∧
      residue A (π ^ (v.depth - j) * v.b) = residue A (π ^ (w.depth - j) * w.b) := by
  simpa only [Nat.zero_add] using
    finitePointSpecialization_earlier_residues A D.uniformizer_ne_zero
    (splitResolutionData A D) j hj P Q v (by simpa using hv) w (by simpa using hw)
    (resolvedSplitSmoothPoint_eq_at_stage A D j hj he)

end FLT.Mazur.WeierstrassDividedDepth
