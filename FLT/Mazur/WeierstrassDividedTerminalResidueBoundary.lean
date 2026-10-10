/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenNormalization
public import FLT.Mazur.WeierstrassDividedTerminalResidueCharts
public import FLT.Mazur.WeierstrassDividedGlobalResidueOverlap

/-!
# Full terminal boundaries and the normalized global gluing maps

For both parity cases, localize at the normalized image of the original
horizontal function. These are the entire original principal opens. The
transition from the successive chart retains the actual global gluing square.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
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

section Laurent
variable (hp : 2 * (start + j + 1) = depth)
local notation "e" => WeierstrassDilatation.residueLaurentEquiv D (start + (j + 1)) hk' hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

/-- The complete original horizontal boundary in normalized laurent coordinates. -/
def terminalLaurentBoundaryIso : Spec (.of (Localization.Away ((e) tx))) ≅
    Spec (.of (Localization.Away tx)) :=
  PrincipalOpenNormalization.specIso e tx

/-- The normalized boundary restricts all original functions on the actual global chart. -/
theorem terminalLaurentBoundaryIso_chart :
    (terminalLaurentBoundaryIso data D j hj hk hp).hom ≫
      PrincipalOpenTensor.inclusion K x ≫ globalDividedTensorChart hπ data K (j + 1) hj =
    Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away ((e) tx)))) ≫
      terminalLaurentChart hπ data D (j + 1) hj hk' hk hp :=
  PrincipalOpenNormalization.specIso_chart e tx _

/-- The entire actual successive overlap maps to the normalized terminal boundary. -/
def terminalLaurentBoundaryTransition :
    Spec (.of (Localization.Away
      (WeierstrassSuccessiveX.tensorCoord W (π ^ (start + j)) π
        (Data.b3 d) (Data.b4 d) (Data.b6 d) K 0))) ≅
          Spec (.of (Localization.Away ((e) tx))) :=
  Scheme.Spec.mapIso (AlgEquiv.toRingEquiv m).toCommRingCatIso.op ≪≫
    (terminalLaurentBoundaryIso data D j hj hk hp).symm

/-- The full normalized transition is the original global gluing map. -/
theorem terminalLaurentBoundaryTransition_chart :
    (terminalLaurentBoundaryTransition data D j hj hk0 hk hp).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away ((e) tx)))) ≫
        terminalLaurentChart hπ data D (j + 1) hj hk' hk hp =
      PrincipalOpenTensor.inclusion K t ≫ globalSuccessiveTensorChart hπ data K j hj := by
  rw [← terminalLaurentBoundaryIso_chart hπ data D j hj hk hp]
  change (_ ≫ (terminalLaurentBoundaryIso data D j hj hk hp).inv) ≫
    (terminalLaurentBoundaryIso data D j hj hk hp).hom ≫ _ = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact globalResidue_middleOverlap hπ data D j hj hk0 hk
end Laurent

section Node
variable (hp : 2 * (start + j + 1) < depth)
local notation "e" => WeierstrassDilatation.residuePolygonEquiv D (start + (j + 1)) hk' hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

/-- The complete original horizontal boundary in normalized node coordinates. -/
def terminalNodeBoundaryIso : Spec (.of (Localization.Away ((e) tx))) ≅
    Spec (.of (Localization.Away tx)) :=
  PrincipalOpenNormalization.specIso e tx

/-- The normalized boundary restricts all original functions on the actual global chart. -/
theorem terminalNodeBoundaryIso_chart :
    (terminalNodeBoundaryIso data D j hj hk hp).hom ≫
      PrincipalOpenTensor.inclusion K x ≫ globalDividedTensorChart hπ data K (j + 1) hj =
    Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away ((e) tx)))) ≫
      terminalNodeChart hπ data D (j + 1) hj hk' hk hp :=
  PrincipalOpenNormalization.specIso_chart e tx _

/-- The entire actual successive overlap maps to the normalized terminal boundary. -/
def terminalNodeBoundaryTransition :
    Spec (.of (Localization.Away
      (WeierstrassSuccessiveX.tensorCoord W (π ^ (start + j)) π
        (Data.b3 d) (Data.b4 d) (Data.b6 d) K 0))) ≅
          Spec (.of (Localization.Away ((e) tx))) :=
  Scheme.Spec.mapIso (AlgEquiv.toRingEquiv m).toCommRingCatIso.op ≪≫
    (terminalNodeBoundaryIso data D j hj hk hp).symm

/-- The full normalized transition is the original global gluing map. -/
theorem terminalNodeBoundaryTransition_chart :
    (terminalNodeBoundaryTransition data D j hj hk0 hk hp).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away ((e) tx)))) ≫
        terminalNodeChart hπ data D (j + 1) hj hk' hk hp =
      PrincipalOpenTensor.inclusion K t ≫ globalSuccessiveTensorChart hπ data K j hj := by
  rw [← terminalNodeBoundaryIso_chart hπ data D j hj hk hp]
  change (_ ≫ (terminalNodeBoundaryIso data D j hj hk hp).inv) ≫
    (terminalNodeBoundaryIso data D j hj hk hp).hom ≫ _ = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact globalResidue_middleOverlap hπ data D j hj hk0 hk
end Node

end FLT.Mazur.WeierstrassDividedDepth
