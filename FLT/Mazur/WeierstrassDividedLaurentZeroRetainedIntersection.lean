/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalZeroConicIntersection
public import FLT.Mazur.WeierstrassSuccessiveXTerminalLaurentComponent

/-!
# The complete Laurent and retained tensor intersection

The actual conic incidence open presents the entire intersection with the
full zero-depth retained chart. Maps induced by one terminal component
therefore agree on this full intersection, not merely on geometric points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth) (hp : 2 * (start + j + 1) = depth)
  (hzero : start + j = 0)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "g" => globalSuccessiveTensorChart hπ data K j hj
local notation "T" => terminalLaurentChart hπ data D (j + 1) hj (by omega) hk hp
local notation "ψ" => residueLaurentConicMap D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp
local notation "q" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "E" => zeroResidueConicBoundaryIso D (start + j) hzero hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "b" => Iso.hom E ≫ PrincipalOpenTensor.inclusion K t
local notation "C" => zeroResidueConicImmersion D (start + j) hzero hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "P" => laurentConicComponent D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp
local notation "l" => laurentConicComponentConic D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp
local notation "r" => laurentConicComponentTorus D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp

/-- The incidence open is the full intersection with the entire zero-depth retained chart. -/
theorem terminalLaurentZeroRetained_isPullback : IsPullback q b T g := by
  apply IsOpenImmersion.isPullback
  · rw [Category.assoc, zeroResidueConicBoundaryIso_inclusion_assoc]
    exact (terminalLaurentZeroConicCoordinates_chart hπ data D j hj hzero hk hp).symm
  · apply TopologicalSpace.Opens.ext
    change g ⁻¹' Set.range T = Set.range b
    rw [terminalLaurentChart_range, globalTensor_depthOverlap_preimage]
    symm
    change Set.range (fun z => PrincipalOpenTensor.inclusion K t ((E).hom z)) = _
    simpa only [Function.comp_def, Scheme.Hom.homeomorph_apply] using
      (E).hom.homeomorph.surjective.range_comp (PrincipalOpenTensor.inclusion K t)

/-- The whole Laurent overlap is compatible when both conic restrictions come from one map. -/
theorem terminalLaurentZeroRetained_compatible_of_conic
    {Y : Scheme.{u}} (f : P ⟶ Y)
    (fRet : Spec (.of (ScalarExtension W (π ^ (start + j)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) K)) ⟶ Y)
    (hc : C ≫ fRet = l ≫ f) :
    pullback.fst T g ≫ r ≫ f = pullback.snd T g ≫ fRet := by
  let H := terminalLaurentZeroRetained_isPullback hπ data D j hj hk hp hzero
  apply (cancel_epi H.isoPullback.hom).mp
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]
  simp only [Category.assoc]
  rw [zeroResidueConicBoundaryIso_inclusion_assoc]
  simp only [hc]
  exact congrArg (fun m => m ≫ f)
    (laurentConicComponent_condition D (start + j) hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e)
      (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp).symm

end FLT.Mazur.WeierstrassDividedDepth
