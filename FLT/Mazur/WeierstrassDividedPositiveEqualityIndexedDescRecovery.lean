/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorDescRecovery
public import FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalDescRecovery
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorIndexedDesc
public import FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalIndexedDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorIndexedDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalIndexedDesc

/-!
# Positive-start descent recovers all original retained indexed inclusions

The original two-node covers identify the descended maps with every complete
retained atlas inclusion, with all source and target index transports explicit.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "F" => fun i => Over.Hom.left (Z i)
local notation "w" => positiveEqualityCycleComponent_scheme_endpoints hπ data D s hs hstart hk hp

section Earlier
variable (j : Fin s)
local notation "T" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := j.val + 1 + (s - j.val)) (by omega) hs (by omega)
  (Fin.succ (Fin.mk (s - j.val + 1) (by omega)))
  (Fin.mk (s - j.val + 2) (by omega)) (by rfl))
local notation "U" => olderIndexedNodeOpenCover hπ data D j.val (by omega)
  (s - j.val) (by omega) (by omega) (by omega)
local notation "M" => globalTensorAtlasMap hπ data K (s + 1) hs
  (Fin.mk (s - j.val + 2) (by omega))
local notation "Q" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (a := j.val + 1 + (s - j.val)) (by omega) hs (by omega))

/-- The first retained atlas restriction has its exact original global target transport. -/
@[reassoc] theorem positiveEqualityRetainedIndexed_first_global :
    (U).f (0 : Fin 2) ≫ T ≫ M =
      olderGlobalResidueFirstNode hπ data D j.val (by omega)
        (s - j.val) (by omega) (by omega) (by omega) ≫ Q := by
  rw [globalTensorAtlasMap_index_transport hπ data
    (a := j.val + 1 + (s - j.val)) (by omega) hs (by omega)
    (Fin.succ ⟨s - j.val + 1, by omega⟩) ⟨s - j.val + 2, by omega⟩ (by rfl)]
  exact olderIndexedNodeMap_first_global_assoc hπ data D j.val (by omega)
    (s - j.val) (by omega) (by omega) (by omega) Q

/-- The second retained atlas restriction has its exact original global target transport. -/
@[reassoc] theorem positiveEqualityRetainedIndexed_second_global :
    (U).f (1 : Fin 2) ≫ T ≫ M =
      olderGlobalResidueSecondNode hπ data D j.val (by omega)
        (s - j.val) (by omega) (by omega) (by omega) ≫ Q := by
  rw [globalTensorAtlasMap_index_transport hπ data
    (a := j.val + 1 + (s - j.val)) (by omega) hs (by omega)
    (Fin.succ ⟨s - j.val + 1, by omega⟩) ⟨s - j.val + 2, by omega⟩ (by rfl)]
  exact olderIndexedNodeMap_second_global_assoc hπ data D j.val (by omega)
    (s - j.val) (by omega) (by omega) (by omega) Q

/-- Descent on the actual family recovers every complete earlier retained atlas inclusion. -/
theorem positiveEqualityCycleInteriorIndexedDesc_original :
    positiveEqualityCycleInteriorIndexedDesc hπ data D s hs hstart hk j F w = M := by
  apply (cancel_epi T).mp
  apply (U).hom_ext
  intro i
  change Fin 2 at i
  fin_cases i
  · exact (positiveEqualityCycleInteriorIndexedDesc_first
      hπ data D s hs hstart hk j F w).trans
      ((positiveEqualityCycleInteriorFirstLocalDesc_original
        hπ data D s hs hstart hk hp j).trans
        (positiveEqualityRetainedIndexed_first_global hπ data D s hs hstart hp j).symm)
  · exact (positiveEqualityCycleInteriorIndexedDesc_second
      hπ data D s hs hstart hk j F w).trans
      ((positiveEqualityCycleInteriorSecondLocalDesc_original
        hπ data D s hs hstart hk hp j).trans
        (positiveEqualityRetainedIndexed_second_global hπ data D s hs hstart hp j).symm)

end Earlier

/-- The original full terminal indexed inclusion is recovered even in the smallest cycle. -/
theorem positiveEqualityCycleTerminalIndexedDesc_original :
    positiveEqualityCycleTerminalIndexedDesc hπ data D s hs hstart hk hp F w =
      globalTensorAtlasMap hπ data K (s + 1) hs ⟨2, by omega⟩ := by
  apply (olderIndexedNodeOpenCover hπ data D s hs 0 hs (by omega) hk).hom_ext
  intro i
  change Fin 2 at i
  fin_cases i
  · change olderIndexedNodeMap _ _ _ _ _ _ _ _ _ 0 ≫ _ =
      olderIndexedNodeMap _ _ _ _ _ _ _ _ _ 0 ≫ _
    erw [positiveEqualityCycleTerminalIndexedDesc_first, olderIndexedNodeMap_first_global,
      positiveEqualityCycleTerminalFirstDesc_original]
  · change olderIndexedNodeMap _ _ _ _ _ _ _ _ _ 1 ≫ _ =
      olderIndexedNodeMap _ _ _ _ _ _ _ _ _ 1 ≫ _
    erw [positiveEqualityCycleTerminalIndexedDesc_second, olderIndexedNodeMap_second_global,
      positiveEqualityCycleTerminalSecondDesc_original]

end FLT.Mazur.WeierstrassDividedDepth
