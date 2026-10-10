/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalFullConicIntersection
public import FLT.Mazur.WeierstrassDividedGlobalConicCoordinates
public import FLT.Mazur.WeierstrassSuccessiveXTerminalConicParameters

/-!
# Exact normalized terminal maps on the retained conic

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
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) K
local notation "t" => WeierstrassSuccessiveX.coord W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) 0
local notation "m" => WeierstrassSuccessiveX.residueMiddleTransition D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "hk'" => Nat.zero_lt_succ (start + j)

open WeierstrassSuccessiveX WeierstrassModificationX
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 d)
local notation "B" => MiddleConicOpen W₀ c
local notation "C₀" => ConicCoordinate (WeierstrassCurve.a₁ W₀) c
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ B))
local notation "C" => residueSuccessiveConicImmersion D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "g" => globalSuccessiveTensorChart hπ data K j hj
local notation "E" => residueConicBoundaryIso D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)

local notation "φ" => residueDividedConicMap D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "f" => globalDividedTensorChart hπ data K (j + 1) hj

section Laurent
variable (hp : 2 * (start + j + 1) = depth)
local notation "e" => WeierstrassDilatation.residueLaurentEquiv D (start + (j + 1)) hk' hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away ((e) tx))))
local notation "G" => terminalLaurentChart hπ data D (j + 1) hj hk' hk hp
local notation "ψ" => residueLaurentConicMap D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

/-- The explicit normalized functions retain the actual global conic immersion. -/
theorem terminalLaurentConicCoordinates_chart :
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
  exact globalDividedConicCoordinates_chart hπ data D j hj hk0 hk

include hπ in
/-- The normalized spectrum map is the complete terminal boundary with its fixed orientation. -/
theorem terminalLaurentConicCoordinates_eq_boundary :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ)) =
      (terminalLaurentConicBoundaryIso data D j hj hk0 hk hp).hom ≫ b := by
  apply (cancel_mono G).mp
  rw [terminalLaurentConicCoordinates_chart hπ data D j hj hk0 hk hp, Category.assoc,
    terminalLaurentConicBoundaryIso_chart]

/-- The explicit oriented parameter map presents the entire terminal-conic intersection. -/
theorem terminalLaurentConicCoordinates_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))) i G (C ≫ g) := by
  rw [terminalLaurentConicCoordinates_eq_boundary hπ data D j hj hk0 hk hp]
  exact terminalLaurentFullConic_isPullback hπ data D j hj hk0 hk hp

end Laurent

section Node
variable (hp : 2 * (start + j + 1) < depth)
local notation "e" => WeierstrassDilatation.residuePolygonEquiv D (start + (j + 1)) hk' hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away ((e) tx))))
local notation "G" => terminalNodeChart hπ data D (j + 1) hj hk' hk hp
local notation "ψ" => residueNodeConicMap D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

/-- The explicit normalized functions retain the actual global conic immersion. -/
theorem terminalNodeConicCoordinates_chart :
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
  exact globalDividedConicCoordinates_chart hπ data D j hj hk0 hk

include hπ in
/-- The normalized spectrum map is the complete terminal boundary with its fixed orientation. -/
theorem terminalNodeConicCoordinates_eq_boundary :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ)) =
      (terminalNodeConicBoundaryIso data D j hj hk0 hk hp).hom ≫ b := by
  apply (cancel_mono G).mp
  rw [terminalNodeConicCoordinates_chart hπ data D j hj hk0 hk hp, Category.assoc,
    terminalNodeConicBoundaryIso_chart]

/-- The explicit oriented parameter map presents the entire terminal-conic intersection. -/
theorem terminalNodeConicCoordinates_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))) i G (C ≫ g) := by
  rw [terminalNodeConicCoordinates_eq_boundary hπ data D j hj hk0 hk hp]
  exact terminalNodeFullConic_isPullback hπ data D j hj hk0 hk hp

end Node

end FLT.Mazur.WeierstrassDividedDepth
