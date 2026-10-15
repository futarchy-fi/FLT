/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGenericAmbient

/-!
# The original graph ideal is the kernel of the entire generic ambient inclusion

The smooth generic graph maps into the generic ambient relation, while the
whole generic ambient relation factors through the complete smooth graph.
These actual factorizations identify their full ideal sheaves. No reduction
or flatness of the adic ambient relation is used.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "V" => completeIdentityActionSmoothOpen K n h
local notation "f" => completeIdentityActionSmoothGraph K n h
local notation "g" => completeIdentityActionGenericSmoothGraph K n h
local notation "u" => completeIdentityActionGenericSmoothInclusion K n h
local notation "v" => completeIdentityActionSecond K n h
local notation "π" => exactVeroneseProjToBase K n h
local notation "s" => completeIdentityActionLiftSpaceStructure K n h
local notation "r" => completeIdentityActionGenericAmbientInclusion K n h
local notation "l" => completeIdentityActionGenericAmbientToSmooth K n h
local notation "b" => Spec.map
  (CommRingCat.ofHom (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))

/-- The smooth generic graph retains its actual original generic coefficient morphism. -/
def completeIdentityGenericSmoothToAmbient :
    completeIdentityActionGenericSmoothInput K n h ⟶
      completeIdentityActionGenericAmbient K n h :=
  pullback.lift (g) (pullback.snd ((V).ι ≫ (v) ≫ (π)) (b)) (by
    rw [completeIdentityActionGenericSmoothGraph, Category.assoc,
      completeIdentityActionLiftSpaceStructure,
      completeIdentityActionSmoothGraph_fst_assoc]
    exact pullback.condition)
local notation "j" => completeIdentityGenericSmoothToAmbient K n h

/-- The factorization retains the exact original generic smooth graph map. -/
@[reassoc] theorem completeIdentityGenericSmoothToAmbient_inclusion : (j) ≫ (r) = (g) :=
  pullback.lift_fst _ _ _

instance completeIdentityActionGenericAmbient_quasiCompact : QuasiCompact (r) := inferInstance

/-- The full graph ideal is exactly the full kernel of the original ambient generic fiber. -/
theorem completeIdentityActionGenericAmbient_kernel : (r).ker = (f).ker := by
  apply le_antisymm
  · calc
      (r).ker ≤ ((j) ≫ (r)).ker := (j).le_ker_comp (r)
      _ = (g).ker := congrArg Scheme.Hom.ker
        (completeIdentityGenericSmoothToAmbient_inclusion K n h)
      _ = (f).ker := completeIdentityActionGenericSmoothGraph_kernel K n h
  · calc
      (f).ker ≤ ((l) ≫ (f)).ker := (l).le_ker_comp (f)
      _ = (r).ker := congrArg Scheme.Hom.ker
        (completeIdentityActionGenericAmbientToSmooth_graph K n h)

/-- Every original affine graph equation is precisely an ambient generic-fiber equation. -/
theorem completeIdentityActionGenericAmbient_affineKernel
    (W : (completeIdentityActionLiftSpace K n h).affineOpens) :
    RingHom.ker ((r).app W).hom = RingHom.ker ((g).app W).hom := by
  rw [← Scheme.Hom.ker_apply, ← Scheme.Hom.ker_apply,
    completeIdentityActionGenericAmbient_kernel, completeIdentityActionGenericSmoothGraph_kernel]

/-- The original adic graph keeps the kernel of the entire ambient generic fiber. -/
theorem completeIdentityActionGraphAdicChart_ambientGenericIdeal (m : ℕ) (i j₀ : Fin n) :
    (r).ker.comap (completeIdentityActionAdicChartSpaceMap K n h m i j₀ ≫
      completeIdentityActionAdicLiftSpaceMap K n h m) =
      (completeIdentityActionGraphAdicChartEmbedding K n h m i j₀).ker := by
  rw [completeIdentityActionGenericAmbient_kernel,
    completeIdentityActionGraphAdicChart_smoothIdeal]

end FLT.Mazur.PolygonInfinitesimalStages
