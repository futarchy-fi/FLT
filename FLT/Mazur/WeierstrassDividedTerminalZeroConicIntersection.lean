/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalResidueCharts
public import FLT.Mazur.WeierstrassDividedGlobalZeroConicIntersection
public import FLT.Mazur.WeierstrassSuccessiveXTerminalConicParameters

/-!
# Exact terminal intersections with the original initial conic

The spectra of the original oriented parameter maps are exactly the full
terminal boundary inclusions. Cancellation uses the actual terminal chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "t" => WeierstrassSuccessiveX.coord W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) 0
local notation "hk'" => Nat.zero_lt_succ (start + j)

open WeierstrassSuccessiveX WeierstrassModificationX
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 d)
local notation "B" => MiddleConicOpen W₀ c
local notation "C₀" => ConicCoordinate (WeierstrassCurve.a₁ W₀) c
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ B))
local notation "C" => zeroResidueConicImmersion D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "g" => globalSuccessiveTensorChart hπ data K j hj

local notation "φ" => residueDividedConicMap D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "f" => globalDividedTensorChart hπ data K (j + 1) hj

section Laurent
variable (hp : 2 * (start + j + 1) = depth)
local notation "e" => WeierstrassDilatation.residueLaurentEquiv D (start + (j + 1)) hk' hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "G" => terminalLaurentChart hπ data D (j + 1) hj hk' hk hp
local notation "ψ" => residueLaurentConicMap D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

/-- The explicit normalized functions retain the actual global conic immersion. -/
theorem terminalLaurentZeroConicCoordinates_chart :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ)) ≫ G = i ≫ C ≫ g := by
  have H : Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ)) ≫
      (WeierstrassDilatation.residueLaurentIso D (start + (j + 1)) hk' hk
        (Data.b3 d) (Data.b4 d) (Data.b6 d)
        (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp).hom =
      Spec.map (CommRingCat.ofHom (AlgHom.toRingHom φ)) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    exact congrArg (fun z => φ z) ((e).symm_apply_apply z)
  rw [terminalLaurentChart, ← Category.assoc, H]
  exact globalZeroDividedConicCoordinates_chart hπ data D j hj hk0 hk

/-- The original incidence open is the whole normalized terminal intersection. -/
theorem terminalLaurentZeroConicCoordinates_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))) i G (C ≫ g) := by
  let _ : IsOpenImmersion i := IsOpenImmersion.of_isLocalization
    (conicT (WeierstrassCurve.a₁ W₀) c)
  apply IsOpenImmersion.isPullback
  · exact (terminalLaurentZeroConicCoordinates_chart hπ data D j hj hk0 hk hp).symm.trans
      (Category.assoc _ _ _).symm
  · apply TopologicalSpace.Opens.ext
    change (C ≫ g) ⁻¹' Set.range G = Set.range i
    rw [terminalLaurentChart_range]
    exact globalZeroDividedConic_preimage hπ data D j hj hk0 hk

/-- The full terminal fiber product is canonically the original initial conic open. -/
def terminalLaurentZeroConicPullbackIso :=
  (terminalLaurentZeroConicCoordinates_isPullback hπ data D j hj hk0 hk hp).isoPullback

end Laurent

section Node
variable (hp : 2 * (start + j + 1) < depth)
local notation "e" => WeierstrassDilatation.residuePolygonEquiv D (start + (j + 1)) hk' hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "G" => terminalNodeChart hπ data D (j + 1) hj hk' hk hp
local notation "ψ" => residueNodeConicMap D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

/-- The explicit normalized functions retain the actual global conic immersion. -/
theorem terminalNodeZeroConicCoordinates_chart :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ)) ≫ G = i ≫ C ≫ g := by
  have H : Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ)) ≫
      (WeierstrassDilatation.residueNodeIso D (start + (j + 1)) hk' hk
        (Data.b3 d) (Data.b4 d) (Data.b6 d)
        (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp).hom =
      Spec.map (CommRingCat.ofHom (AlgHom.toRingHom φ)) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    exact congrArg (fun z => φ z) ((e).symm_apply_apply z)
  rw [terminalNodeChart, ← Category.assoc, H]
  exact globalZeroDividedConicCoordinates_chart hπ data D j hj hk0 hk

/-- The original incidence open is the whole normalized terminal intersection. -/
theorem terminalNodeZeroConicCoordinates_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))) i G (C ≫ g) := by
  let _ : IsOpenImmersion i := IsOpenImmersion.of_isLocalization
    (conicT (WeierstrassCurve.a₁ W₀) c)
  apply IsOpenImmersion.isPullback
  · exact (terminalNodeZeroConicCoordinates_chart hπ data D j hj hk0 hk hp).symm.trans
      (Category.assoc _ _ _).symm
  · apply TopologicalSpace.Opens.ext
    change (C ≫ g) ⁻¹' Set.range G = Set.range i
    rw [terminalNodeChart_range]
    exact globalZeroDividedConic_preimage hπ data D j hj hk0 hk

/-- The full terminal fiber product is canonically the original initial conic open. -/
def terminalNodeZeroConicPullbackIso :=
  (terminalNodeZeroConicCoordinates_isPullback hπ data D j hj hk0 hk hp).isoPullback

end Node

end FLT.Mazur.WeierstrassDividedDepth
