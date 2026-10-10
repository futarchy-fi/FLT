/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalConicBoundary
public import FLT.Mazur.WeierstrassDividedGlobalConicIntersection

/-!
# Full terminal-chart intersections with the retained conic

Both complete normalized terminal charts intersect the original conic in
precisely its incidence open. The projections use the existing terminal
boundary isomorphisms and retain their exact global maps.
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
local notation "T" => Iso.hom (terminalLaurentConicBoundaryIso data D j hj hk0 hk hp) ≫ b

/-- The complete laurent terminal chart has no additional intersection with the conic. -/
theorem terminalLaurentFullConic_preimage : (C ≫ g) ⁻¹' Set.range G = Set.range i := by
  rw [terminalLaurentChart_range]
  exact globalDividedConic_preimage hπ data D j hj hk0 hk

/-- The original incidence open is the entire terminal-laurent and conic fiber product. -/
theorem terminalLaurentFullConic_isPullback : IsPullback T i G (C ≫ g) := by
  let _ : IsOpenImmersion i := IsOpenImmersion.of_isLocalization
    (conicT (WeierstrassCurve.a₁ W₀) c)
  apply IsOpenImmersion.isPullback
  · exact (terminalLaurentConicBoundaryIso_chart hπ data D j hj hk0 hk hp).symm.trans
      (Category.assoc _ _ _).symm
  · exact TopologicalSpace.Opens.ext
      (terminalLaurentFullConic_preimage hπ data D j hj hk0 hk hp)

/-- The full laurent intersection is canonically the original conic incidence open. -/
def terminalLaurentFullConicPullbackIso : Spec (.of B) ≅ pullback G (C ≫ g) :=
  (terminalLaurentFullConic_isPullback hπ data D j hj hk0 hk hp).isoPullback

/-- The full intersection comparison retains its exact terminal boundary map. -/
theorem terminalLaurentFullConicPullbackIso_terminal :
    (terminalLaurentFullConicPullbackIso hπ data D j hj hk0 hk hp).hom ≫
      pullback.fst G (C ≫ g) = T :=
  (terminalLaurentFullConic_isPullback hπ data D j hj hk0 hk hp).isoPullback_hom_fst

/-- The full intersection comparison retains its original conic inclusion. -/
theorem terminalLaurentFullConicPullbackIso_conic :
    (terminalLaurentFullConicPullbackIso hπ data D j hj hk0 hk hp).hom ≫
      pullback.snd G (C ≫ g) = i :=
  (terminalLaurentFullConic_isPullback hπ data D j hj hk0 hk hp).isoPullback_hom_snd

end Laurent

section Node
variable (hp : 2 * (start + j + 1) < depth)
local notation "e" => WeierstrassDilatation.residuePolygonEquiv D (start + (j + 1)) hk' hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away ((e) tx))))
local notation "G" => terminalNodeChart hπ data D (j + 1) hj hk' hk hp
local notation "T" => Iso.hom (terminalNodeConicBoundaryIso data D j hj hk0 hk hp) ≫ b

/-- The complete node terminal chart has no additional intersection with the conic. -/
theorem terminalNodeFullConic_preimage : (C ≫ g) ⁻¹' Set.range G = Set.range i := by
  rw [terminalNodeChart_range]
  exact globalDividedConic_preimage hπ data D j hj hk0 hk

/-- The original incidence open is the entire terminal-node and conic fiber product. -/
theorem terminalNodeFullConic_isPullback : IsPullback T i G (C ≫ g) := by
  let _ : IsOpenImmersion i := IsOpenImmersion.of_isLocalization
    (conicT (WeierstrassCurve.a₁ W₀) c)
  apply IsOpenImmersion.isPullback
  · exact (terminalNodeConicBoundaryIso_chart hπ data D j hj hk0 hk hp).symm.trans
      (Category.assoc _ _ _).symm
  · exact TopologicalSpace.Opens.ext
      (terminalNodeFullConic_preimage hπ data D j hj hk0 hk hp)

/-- The full node intersection is canonically the original conic incidence open. -/
def terminalNodeFullConicPullbackIso : Spec (.of B) ≅ pullback G (C ≫ g) :=
  (terminalNodeFullConic_isPullback hπ data D j hj hk0 hk hp).isoPullback

/-- The full intersection comparison retains its exact terminal boundary map. -/
theorem terminalNodeFullConicPullbackIso_terminal :
    (terminalNodeFullConicPullbackIso hπ data D j hj hk0 hk hp).hom ≫
      pullback.fst G (C ≫ g) = T :=
  (terminalNodeFullConic_isPullback hπ data D j hj hk0 hk hp).isoPullback_hom_fst

/-- The full intersection comparison retains its original conic inclusion. -/
theorem terminalNodeFullConicPullbackIso_conic :
    (terminalNodeFullConicPullbackIso hπ data D j hj hk0 hk hp).hom ≫
      pullback.snd G (C ≫ g) = i :=
  (terminalNodeFullConic_isPullback hπ data D j hj hk0 hk hp).isoPullback_hom_snd

end Node

end FLT.Mazur.WeierstrassDividedDepth
