/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedLaurentTerminalOpenExclusions
public import FLT.Mazur.WeierstrassDividedPrecedingAtlasRange
public import FLT.Mazur.WeierstrassDividedZeroEqualityAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityAtlasCompatibility

/-!
# Empty terminal overlaps in the original equality-depth atlas

The entire Laurent atlas chart lies in the complete terminal component.
Its positive-scale exclusions give empty scheme intersections with infinity
and with every retained chart beyond its immediate neighbor.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
local notation "J" => terminalLaurentAtlasIso hπ data D (s + 1) hs (by omega) hk hp
local notation "T" => laurentTerminalProjectiveComponent hπ data D s hs hk hp

/-- Every point of the whole Laurent atlas object comes from the complete terminal component. -/
theorem terminalLaurentAtlas_range_subset_component :
    Set.range (m (Fin.succ 0)) ⊆ Set.range T := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨a, rfl⟩ := (J).hom.homeomorph.surjective z
  refine ⟨(ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) a, ?_⟩
  have H := (laurentTerminalProjectiveComponent_torus hπ data D s hs hk hp).trans
    (terminalLaurentAtlasIso_map hπ data D (s + 1) hs (by omega) hk hp).symm
  exact congrArg (fun f => f a) H

include D hk hp in
/-- At positive scale the full terminal atlas chart misses infinity. -/
theorem zeroEqualityAtlas_terminal_infinity_disjoint (hpos : 0 < start + s) :
    Disjoint (Set.range (m (Fin.succ 0))) (Set.range (m 0)) :=
  (laurentTerminalProjectiveComponent_infinity_disjoint hπ data D s hs hk hp hpos).mono_left
    (terminalLaurentAtlas_range_subset_component hπ data D s hs hk hp)

include D hk hp in
/-- Every original chart beyond the terminal neighbor misses the whole terminal atlas object. -/
theorem zeroEqualityAtlas_terminal_nonadjacent_disjoint (hpos : 0 < start + s)
    (k : Fin (s + 1 + 3)) (hk3 : 3 ≤ k.val) :
    Disjoint (Set.range (m (Fin.succ 0))) (Set.range (m k)) := by
  let i : Fin (s + 1) := ⟨k.val - 3, by omega⟩
  have H := precedingGlobalTensorAtlas_range_subset hπ data s hs 0 hs K i
  have hi : (Fin.succ ⟨i.val + 1 + 0 + 1, by omega⟩ : Fin (s + 1 + 0 + 3)) =
      k := Fin.ext (by dsimp [i]; omega)
  rw [hi] at H
  exact ((laurentTerminalProjectiveComponent_precedingExterior_disjoint
    hπ data D s hs hk hp hpos).mono_left
    (terminalLaurentAtlas_range_subset_component hπ data D s hs hk hp)).mono_right H

variable (hstart : start = 0) (hpos : 0 < s) {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "C" => ZeroEqualityPositiveAtlasCompatible hπ data D s hs hstart hk hp hpos F w

/-- Terminal versus infinity compatibility holds on the actual empty scheme intersection. -/
theorem zeroEqualityPositiveAtlasCompatible_terminal_infinity : C (Fin.succ 0) 0 := by
  let _ := Scheme.isEmpty_pullback _ _
    (zeroEqualityAtlas_terminal_infinity_disjoint hπ data D s hs hk hp (by omega))
  exact isInitialOfIsEmpty.hom_ext _ _

/-- Every nonadjacent terminal overlap satisfies the full scheme compatibility equation. -/
theorem zeroEqualityPositiveAtlasCompatible_terminal_nonadjacent
    (k : Fin (s + 1 + 3)) (hk3 : 3 ≤ k.val) : C (Fin.succ 0) k := by
  let _ := Scheme.isEmpty_pullback _ _
    (zeroEqualityAtlas_terminal_nonadjacent_disjoint hπ data D s hs hk hp (by omega) k hk3)
  exact isInitialOfIsEmpty.hom_ext _ _

end FLT.Mazur.WeierstrassDividedDepth
