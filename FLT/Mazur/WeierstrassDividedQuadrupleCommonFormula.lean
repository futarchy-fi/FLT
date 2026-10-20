/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedQuadrupleCommonModel

/-!
# Local formulas for the quadruple-depth common-model output

Restriction to either actual formula chart recovers its output.
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
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (D : SplitNodeDepth W π (4 * k)) (d : Data W π k)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "data" => splitNodeDoubledFamily D
local notation "j" => k + k
local notation "hj" => (le_rfl : k + k ≤ k + k)
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => nodalQuadrupleAdditionOpen D d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

local notation "V" => quadrupleSmoothSourceOpen D d a c
local notation "src" => nodalQuadrupleAdditionSource D d a c
local notation "inc" => nodalQuadrupleAdditionInclusion D d a c
local notation "out" => nodalQuadrupleAdditionOutput D d a c
local notation "C" => Scheme.Opens.iSupOpenCover (fun i => (inc i).opensRange)

/-- A common-source refinement in either local chart has its constructed output. -/
theorem quadrupleCommonOutput_local (i : Bool) {X : Scheme}
    (p : X ⟶ (V).toScheme) (q : X ⟶ src i)
    (hpq : p ≫ (V).ι = q ≫ inc i) :
    p ≫ quadrupleCommonOutput D d a c =
      q ≫ out i := by
  have hi : (C).f i ≫ (O).ι = (inc i).opensRange.ι :=
    Scheme.homOfLE_ι _ (le_iSup (fun i => (inc i).opensRange) i)
  have h : p ≫ Scheme.homOfLE (Spec (.of S)) (show V ≤ O from inf_le_left) =
      q ≫ (inc i).isoOpensRange.hom ≫ (C).f i := by
    apply (cancel_mono (O).ι).mp
    simpa only [Category.assoc, hi, Scheme.homOfLE_ι,
      Scheme.homOfLE_ι_assoc, Scheme.Hom.isoOpensRange_hom_ι] using hpq
  rw [quadrupleCommonOutput, ← Category.assoc, h]
  simp only [Category.assoc, nodalQuadrupleAddition_formula]

end FLT.Mazur.WeierstrassDividedDepth
