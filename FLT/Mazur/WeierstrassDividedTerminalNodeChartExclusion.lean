/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalNodeIncidence
public import FLT.Mazur.WeierstrassDividedGlobalTensorIntersection
public import FLT.Mazur.PrincipalOpenVanishingIntersection
public import FLT.Mazur.WeierstrassDividedResidueAtlasExtension
public import FLT.Mazur.SchemeDisjointBaseChange

/-!
# The terminal origin misses the entire preceding successive chart

The original tensor horizontal function vanishes at the terminal origin.
The full tensor-chart pullback therefore excludes that origin at every depth.
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
  (hk : 2 * (start + j + 1) ≤ depth)
  (hp : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "G" => terminalNodeChart hπ data D (j + 1) hj (by omega) hk hp
local notation "g" => globalSuccessiveTensorChart hπ data K j hj
local notation "o" => PolygonNodePresentation.aOrigin K

local notation "N" => terminalConicNodeSection hπ data D j hj hk hp
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) K
local notation "E" => WeierstrassDilatation.residueNodeIso D (start + (j + 1))
  (by omega) hk (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "e" => WeierstrassDilatation.residuePolygonEquiv D (start + (j + 1))
  (by omega) hk (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

omit [IsBezout R] in
/-- The original tensor boundary excludes the terminal origin before globalization. -/
theorem terminalNodeTensorOrigin_boundary_disjoint :
    Disjoint (Set.range (PrincipalOpenTensor.inclusion K x))
      (Set.range (o ≫ (E).hom)) := by
  have hx : (e) tx = algebraMap K _
      (↑(WeierstrassDilatation.residueTangentUnit D)⁻¹ : K) *
        (PolygonNodeLocalization.y - PolygonNodeLocalization.x) :=
    WeierstrassDilatation.residuePolygonEquiv_x D (start + j + 1)
      (by omega) hk (Data.b3 d) (Data.b4 d) (Data.b6 d)
      (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
  have hz : PolygonNodePresentation.aEval ((e) tx) = 0 := by
    rw [hx]
    simp [PolygonNodePresentation.aEval]
  have H := PrincipalOpenVanishingIntersection.disjoint
    ((PolygonNodePresentation.aEval (R := K)).toRingHom.comp (e).toRingHom) tx hz
  change Disjoint _ (Set.range (Spec.map _ ≫ Spec.map _))
  rw [← Spec.map_comp]
  exact H

/-- The actual terminal node lies outside the whole previous chart, including at depth zero. -/
theorem terminalConicNodeSection_successive_disjoint : Disjoint (Set.range N) (Set.range g) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, rfl⟩ ⟨b, hb⟩
  obtain ⟨v, hv, _⟩ := Scheme.exists_preimage_of_isPullback
    (globalTensor_depthOverlap_isPullback hπ data K j hj) ((E).hom (o a)) b hb.symm
  exact Set.disjoint_left.mp
    (terminalNodeTensorOrigin_boundary_disjoint data D j hj hk hp) ⟨_, hv⟩ ⟨a, rfl⟩

/-- The complete terminal-origin and preceding-chart intersection is the empty scheme. -/
theorem terminalConicNodeSection_successive_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) N g := by
  let _ := Scheme.isEmpty_pullback N g
    (terminalConicNodeSection_successive_disjoint hπ data D j hj hk hp)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback N g)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

/-- Arbitrary coefficient extension preserves the full terminal-node/chart exclusion. -/
theorem terminalExtendedNode_successive_isPullback
    (S : Type u) [CommRing S] [Algebra R S] [Algebra (ResidueField R) S]
    [IsScalarTower R (ResidueField R) S] :
    let ext := globalResidueExtensionMap hπ data S (j + 1) hj
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (pullback.fst ext N) (pullback.fst ext g) :=
  SchemeDisjointBaseChange.isPullback
    (terminalConicNodeSection_successive_disjoint hπ data D j hj hk hp) _

end FLT.Mazur.WeierstrassDividedDepth
