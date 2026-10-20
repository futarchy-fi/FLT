/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalShallowCommonModel

/-!
# Local formulas for the shallow common-model output

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
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 2 * k ≤ m) (hm : m ≤ 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hr : m - 2 * k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (j : ℕ) (hj : j ≤ n) (hkj : k ≤ j) (hrj : m - 2 * k ≤ j)
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => nodalShallowAdditionOpen D hdepth hm data hr d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

local notation "V" => nodalShallowSmoothSourceOpen D hdepth hm data hr d a c
local notation "src" => nodalShallowAdditionSource D hdepth hm data hr d a c
local notation "inc" => nodalShallowAdditionInclusion D hdepth hm data hr d a c
local notation "out" => nodalShallowAdditionOutput D hdepth hm data hr d a c
local notation "C" => Scheme.Opens.iSupOpenCover (fun i => (inc i).opensRange)
local notation "promote" => finiteGlobalSmoothTransition hπ data (m - 2 * k) j hrj hj

/-- A common-source refinement in either local chart has its constructed promoted output. -/
theorem nodalShallowCommonOutput_local (i : Bool) {X : Scheme}
    (p : X ⟶ (V).toScheme) (q : X ⟶ src i)
    (hpq : p ≫ (V).ι = q ≫ inc i) :
    p ≫ nodalShallowCommonOutput D hdepth hm data hr d a c j hj hrj =
      q ≫ out i ≫ promote := by
  have hi : (C).f i ≫ (O).ι = (inc i).opensRange.ι :=
    Scheme.homOfLE_ι _ (le_iSup (fun i => (inc i).opensRange) i)
  have h : p ≫ Scheme.homOfLE (Spec (.of S)) (show V ≤ O from inf_le_left) =
      q ≫ (inc i).isoOpensRange.hom ≫ (C).f i := by
    apply (cancel_mono (O).ι).mp
    simpa only [Category.assoc, hi, Scheme.homOfLE_ι,
      Scheme.homOfLE_ι_assoc, Scheme.Hom.isoOpensRange_hom_ι] using hpq
  rw [nodalShallowCommonOutput, ← Category.assoc, h]
  simp only [Category.assoc, nodalShallowPromotedAddition_formula]

end FLT.Mazur.WeierstrassDividedDepth
