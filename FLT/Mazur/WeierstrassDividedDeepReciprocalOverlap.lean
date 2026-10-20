/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDeepReciprocalTangent
public import FLT.Mazur.WeierstrassDividedDeepReciprocalSecant

/-!
# The full deep-node-common-source overlap with the reciprocal law

Pulling back the actual deep-node tangent/secant cover proves equality on the
whole overlap. Only the source refinement is flat; no output equality is assumed.
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
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ}
  (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hkk : k + k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
variable (j : ℕ) (hj : j ≤ n) (hkj : k + k ≤ j)
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => nodalDeepAdditionOpen D data hkk d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

local notation "V" => deepSmoothSourceOpen D data hkk d a c
local notation "src" => nodalDeepAdditionSource D data hkk d a c
local notation "inc" => nodalDeepAdditionInclusion D data hkk d a c
local notation "out" => nodalDeepAdditionOutput D data hkk d a c
local notation "C" => Scheme.Opens.iSupOpenCover (fun i => (inc i).opensRange)
local notation "promote" => finiteGlobalSmoothTransition hπ data (k + k) j hkj hj

local notation "Ot" => deepNodalTangentBranchOutputOpen D data hkk d a c
local notation "T" => DividedTangentRing W (π ^ k) (d).b3 (d).b4 (d).b6 a c
local notation "e" => IsScalarTower.toAlgHom R S T
local notation "Rcp" => finiteResolvedReciprocalOutputOpen hπ data j hj
local notation "pair" => deepCommonInput D data hkk d a c j hj hkj

/-- Every flat refinement of the entire deep-node/reciprocal overlap has equal outputs. -/
theorem deepCommonOutput_reciprocalOverlap {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme) [Flat q]
    (hpq : p ≫ finiteResolvedReciprocalDomainMap hπ data j hj = q ≫ pair) :
    p ≫ finiteResolvedReciprocalAddition hπ data j hj =
      q ≫ deepCommonOutput D data hkk d a c j hj hkj := by
  let v := Scheme.homOfLE (Spec (.of S)) (show V ≤ O from inf_le_left)
  apply Scheme.Cover.hom_ext ((C).pullback₁ (q ≫ v))
  intro b
  let f := pullback.fst (q ≫ v) ((C).f b)
  let g := pullback.snd (q ≫ v) ((C).f b)
  let r := g ≫ (inc b).isoOpensRange.inv
  have hq : f ≫ q ≫ v = g ≫ (C).f b := pullback.condition
  have hi : (C).f b ≫ (O).ι = (inc b).opensRange.ι :=
    Scheme.homOfLE_ι _ (le_iSup (fun i => (inc i).opensRange) b)
  have he : (f ≫ q) ≫ (V).ι = r ≫ inc b := by
    have h := congrArg (· ≫ (O).ι) hq
    simpa only [r, v, Category.assoc, hi, Scheme.homOfLE_ι,
      Scheme.Hom.isoOpensRange_inv_comp] using h
  have hp : (f ≫ p) ≫ finiteResolvedReciprocalDomainMap hπ data j hj =
      (f ≫ q) ≫ pair := by rw [Category.assoc, hpq, Category.assoc]
  cases b with
  | false =>
    exact deepCommonOutput_reciprocalSecant D data hkk d a c
      j hj hkj (f ≫ p) (f ≫ q) r hp he
  | true =>
    exact deepCommonOutput_reciprocalTangent D data hkk d a c
      j hj hkj (f ≫ p) (f ≫ q) r hp he

end FLT.Mazur.WeierstrassDividedDepth
