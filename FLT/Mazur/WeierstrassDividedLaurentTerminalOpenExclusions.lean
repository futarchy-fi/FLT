/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineOpenChartExclusion
public import FLT.Mazur.WeierstrassDividedLaurentTerminalProjectiveComponent
public import FLT.Mazur.WeierstrassDividedOlderConicExteriorDisjoint
public import FLT.Mazur.WeierstrassDividedOlderResidueInfinity

/-!
# Open exclusions for the complete equality-depth terminal component

The original conic is a nonempty open of the terminal projective line.
Its disjointness from an ambient open therefore excludes the whole component,
including every point supplied by the Laurent chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "a" => WeierstrassCurve.a₁ (W.map (residue R))
local notation "c" => residue R (Data.b6 e)
local notation "l" => laurentConicComponentConic D (start + s) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp
local notation "J" => laurentConicComponentProjectiveIso D (start + s) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp
local notation "C" => laurentTerminalOriginalConic hπ data D s hs hk
local notation "F" => laurentTerminalProjectiveComponent hπ data D s hs hk hp

/-- The actual original conic is enough to test exclusion of an ambient open. -/
theorem laurentTerminalProjectiveComponent_disjoint_of_conic
    {U : Scheme.{u}} (g : U ⟶ finiteGlobalTensorModel hπ data K (s + 1) hs)
    [IsOpenImmersion g] (h : Disjoint (Set.range C) (Set.range g)) :
    Disjoint (Set.range F) (Set.range g) := by
  let p := Spec.map (CommRingCat.ofHom
    (conicFirstIncidencePoint a c (D.a₁_unit.map (residue R))).toRingHom)
  let _ : Nonempty (Spec (.of (ConicCoordinate a c))) := Nonempty.map p inferInstance
  apply ProjectiveLine.map_range_open_disjoint_of_chart K (l ≫ (J).inv) F g
  simpa only [laurentTerminalProjectiveComponent, Category.assoc,
    Iso.inv_hom_id_assoc, laurentTerminalComponentMap_conic] using h

/-- At positive scale the complete original conic is the retained middle conic. -/
theorem laurentTerminalOriginalConic_retained (hpos : 0 < start + s) :
    C = olderGlobalMiddleConic hπ data D s hs 0 hs hpos hk := by
  rw [laurentTerminalOriginalConic_positive hπ data D s hs hk hpos,
    olderGlobalMiddleConic, olderGlobalTensorChart_zero_retention]

/-- The entire equality terminal component misses the preceding exterior. -/
theorem laurentTerminalProjectiveComponent_precedingExterior_disjoint
    (hpos : 0 < start + s) :
    Disjoint (Set.range F)
      (Set.range (olderGlobalExteriorTensorChart hπ data K s hs 0 hs)) := by
  apply laurentTerminalProjectiveComponent_disjoint_of_conic hπ data D s hs hk hp
  rw [laurentTerminalOriginalConic_retained hπ data D s hs hk hpos]
  exact (olderGlobalConicExterior_disjoint hπ data D s hs 0 hs hpos hk).symm

/-- The full positive-scale equality terminal component has no infinity intersection. -/
theorem laurentTerminalProjectiveComponent_infinity_disjoint (hpos : 0 < start + s) :
    Disjoint (Set.range F)
      (Set.range (finiteInfinityTensorChart hπ data K (s + 1) hs)) := by
  apply laurentTerminalProjectiveComponent_disjoint_of_conic hπ data D s hs hk hp
  rw [laurentTerminalOriginalConic_retained hπ data D s hs hk hpos]
  apply (olderGlobalResidue_infinity_disjoint K hπ data s hs 0 hs _ hpos).mono_left
  · rintro _ ⟨z, rfl⟩
    exact ⟨_, rfl⟩
  · exact (residue_eq_zero_iff π).mpr
      (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)

end FLT.Mazur.WeierstrassDividedDepth
