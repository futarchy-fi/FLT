/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueConicBoundaryGeometry
public import FLT.Mazur.WeierstrassDividedTerminalResidueBoundary
public import FLT.Mazur.WeierstrassDividedGlobalResidueOverlap

/-!
# The retained conic meets both normalized terminal boundaries

In both terminal parity cases the entire normalized boundary is isomorphic
to the original conic incidence open. The actual global gluing square keeps
the original conic immersion and all its functions, and is cartesian.
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

section Laurent
variable (hp : 2 * (start + j + 1) = depth)
local notation "e" => WeierstrassDilatation.residueLaurentEquiv D (start + (j + 1)) hk' hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away ((e) tx))))
local notation "G" => terminalLaurentChart hπ data D (j + 1) hj hk' hk hp

/-- The complete laurent boundary is the original conic incidence open. -/
def terminalLaurentConicBoundaryIso : Spec (.of B) ≅
    Spec (.of (Localization.Away ((e) tx))) :=
  E ≪≫ terminalLaurentBoundaryTransition data D j hj hk0 hk hp

/-- The laurent boundary isomorphism keeps the original global conic immersion. -/
theorem terminalLaurentConicBoundaryIso_chart :
    (terminalLaurentConicBoundaryIso data D j hj hk0 hk hp).hom ≫ b ≫ G = i ≫ C ≫ g := by
  change ((E).hom ≫ _) ≫ _ = _
  rw [Category.assoc, terminalLaurentBoundaryTransition_chart,
    residueConicBoundaryIso_inclusion_assoc]

/-- The laurent boundary's full intersection with the conic is its entire original open. -/
theorem terminalLaurentConicBoundary_isPullback :
    IsPullback (terminalLaurentConicBoundaryIso data D j hj hk0 hk hp).hom i
      (b ≫ G) (C ≫ g) :=
  IsPullback.of_horiz_isIso_mono
    ⟨terminalLaurentConicBoundaryIso_chart hπ data D j hj hk0 hk hp⟩

end Laurent

section Node
variable (hp : 2 * (start + j + 1) < depth)
local notation "e" => WeierstrassDilatation.residuePolygonEquiv D (start + (j + 1)) hk' hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away ((e) tx))))
local notation "G" => terminalNodeChart hπ data D (j + 1) hj hk' hk hp

/-- The complete node boundary is the original conic incidence open. -/
def terminalNodeConicBoundaryIso : Spec (.of B) ≅
    Spec (.of (Localization.Away ((e) tx))) :=
  E ≪≫ terminalNodeBoundaryTransition data D j hj hk0 hk hp

/-- The node boundary isomorphism keeps the original global conic immersion. -/
theorem terminalNodeConicBoundaryIso_chart :
    (terminalNodeConicBoundaryIso data D j hj hk0 hk hp).hom ≫ b ≫ G = i ≫ C ≫ g := by
  change ((E).hom ≫ _) ≫ _ = _
  rw [Category.assoc, terminalNodeBoundaryTransition_chart,
    residueConicBoundaryIso_inclusion_assoc]

/-- The node boundary's full intersection with the conic is its entire original open. -/
theorem terminalNodeConicBoundary_isPullback :
    IsPullback (terminalNodeConicBoundaryIso data D j hj hk0 hk hp).hom i
      (b ≫ G) (C ≫ g) :=
  IsPullback.of_horiz_isIso_mono
    ⟨terminalNodeConicBoundaryIso_chart hπ data D j hj hk0 hk hp⟩

end Node

end FLT.Mazur.WeierstrassDividedDepth
