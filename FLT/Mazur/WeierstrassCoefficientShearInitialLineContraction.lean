/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialLineProjection
public import FLT.Mazur.WeierstrassIncidenceShearLineContraction

/-!
# The actual sheared incidence line contracts to its original cubic

Every finite stage has the same complete affine normalization coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
  (hs : algebraMap R S (π ^ start) = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "L" => coefficientShearInitialLine hπ data S r j hj hs h3 h4 hr
local notation "N" => originalShearIncidenceNormalization W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs h3 h4 hr
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)

/-- The entire incidence line has its displayed original cubic contraction at every stage. -/
@[reassoc] theorem coefficientShearInitialLine_toCurve :
    L ≫ coefficientShearGluedProjection hπ data S r j hj ≫
        finiteGlobalContraction hπ data j hj =
      Spec.map (CommRingCat.ofHom (N).toRingHom) ≫
        WeierstrassIntegralChart.integralCurveChart W 2 := by
  rw [coefficientShearInitialLine_projection_assoc, globalInitialChart,
    Category.assoc, finiteLocalChart_contraction, finiteInitialChart_toCurve,
    WeierstrassModificationX.toCurve,
    ← Spec.map_comp_assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
