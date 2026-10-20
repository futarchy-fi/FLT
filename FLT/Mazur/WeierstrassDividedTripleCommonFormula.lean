/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleCommonModel

/-!
# Local formulas for the exact-triple common-model output

Restriction to either actual formula chart recovers its promoted output.
The hypothesis identifies source maps only, without prescribing outputs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure rootShearCurve
  nodalSecondShear nodalSecondQuotient
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
variable (j : ℕ) (hj : j ≤ n) (hkj : k ≤ j)
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => tripleAdditionOpen D data hk a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

local notation "V" => tripleSmoothSourceOpen D data hk a c
local notation "src" => tripleAdditionSource D data hk a c
local notation "inc" => tripleAdditionInclusion D data hk a c
local notation "out" => tripleAdditionOutput D data hk a c
local notation "C" => Scheme.Opens.iSupOpenCover (fun i => (inc i).opensRange)
local notation "promote" => finiteGlobalSmoothTransition hπ data k j hkj hj

/-- A common-source refinement in either local chart has its constructed promoted output. -/
theorem tripleCommonOutput_local (i : Bool) {X : Scheme}
    (p : X ⟶ (V).toScheme) (q : X ⟶ src i)
    (hpq : p ≫ (V).ι = q ≫ inc i) :
    p ≫ tripleCommonOutput D data hk a c j hj hkj =
      q ≫ out i ≫ promote := by
  have hi : (C).f i ≫ (O).ι = (inc i).opensRange.ι :=
    Scheme.homOfLE_ι _ (le_iSup (fun i => (inc i).opensRange) i)
  have h : p ≫ Scheme.homOfLE (Spec (.of S)) (show V ≤ O from inf_le_left) =
      q ≫ (inc i).isoOpensRange.hom ≫ (C).f i := by
    apply (cancel_mono (O).ι).mp
    simpa only [Category.assoc, hi, Scheme.homOfLE_ι,
      Scheme.homOfLE_ι_assoc, Scheme.Hom.isoOpensRange_hom_ι] using hpq
  rw [tripleCommonOutput, ← Category.assoc, h]
  simp only [Category.assoc, triplePromotedAddition_formula]

end FLT.Mazur.WeierstrassDividedDepth
