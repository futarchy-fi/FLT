/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityActionNodeGraph
public import FLT.Mazur.SchematicDenseDedekindFlat

/-!
# Flatness of the actual original action graph

The schematic closure of the original smooth graph has no power-series
scalar torsion. Its flatness follows from the dense flat smooth input,
without replacing the closure by its reduction or assuming a node inverse.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "u" => completeIdentityActionSmoothToGraph K n h
local notation "s" => completeIdentityActionSecond K n h
local notation "π" => exactVeroneseProjToBase K n h

/-- The full schematic graph is Noetherian, including all node-input fibers. -/
instance completeIdentityActionGraph_noetherian :
    IsNoetherian (completeIdentityActionGraphClosure K n h) :=
  Chow.source_isNoetherian (p)

/-- The dense smooth graph is quasi-compact in its actual schematic closure. -/
instance completeIdentityActionSmoothToGraph_quasiCompact : QuasiCompact (u) := by
  let _ : TopologicalSpace.NoetherianSpace
      (completeIdentityActionSmoothOpen K n h).toScheme :=
    TopologicalSpace.NoetherianSpace.set
      (completeIdentityActionSmoothOpen K n h : Set (completeIdentityActionProduct K n h 0))
  exact quasiCompact_of_noetherianSpace_source _

/-- The original graph closure is flat over the literal power-series base. -/
instance completeIdentityActionGraph_base_flat : Flat ((p) ≫ (s) ≫ (π)) := by
  let e := (Scheme.ΓSpecIso (.of (PowerSeries K))).commRingCatIsoToRingEquiv
  let _ : IsDomain Γ(Spec (.of (PowerSeries K)), ⊤) := e.toMulEquiv.isDomain _
  let _ : IsPrincipalIdealRing Γ(Spec (.of (PowerSeries K)), ⊤) :=
    IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
  let _ : Flat ((u) ≫ (p) ≫ (s) ≫ (π)) := by
    rw [completeIdentityActionSmoothToGraph_projection_assoc]
    infer_instance
  exact SchematicDenseDedekindFlat.flat (u) ((p) ≫ (s) ≫ (π))

/-- The constructed polygon-valued graph map has the same flat original-base structure. -/
instance completeIdentityActionGraphLift_base_flat :
    Flat (completeIdentityActionGraphLift K n h ≫ (π)) := by
  rw [completeIdentityActionGraphLift_structure]
  infer_instance

/-- Every full node graph retains flatness over the unchanged original base. -/
instance completeIdentityActionNodeGraph_base_flat (i : Fin n) :
    Flat (completeIdentityActionNodeGraphProjection K n h i ≫
      (completeIdentityActionExtensionOpen K n h (some i)).ι ≫ (s) ≫ (π)) := by
  rw [completeIdentityActionNodeGraphProjection, morphismRestrict_ι_assoc]
  infer_instance

end FLT.Mazur.PolygonInfinitesimalStages
