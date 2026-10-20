/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleReciprocalTangent
public import FLT.Mazur.WeierstrassDividedTripleReciprocalSecant

/-!
# The full exact-triple-common-source overlap with the reciprocal law

Pulling back the actual exact-triple tangent/secant cover proves equality on the
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

local notation "Ot" => tripleTangentBranchOutputOpen D data hk a c
local notation "T" => DividedTangentRing W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a c
local notation "e" => IsScalarTower.toAlgHom R S T
local notation "Rcp" => finiteResolvedReciprocalOutputOpen hπ data j hj
local notation "pair" => tripleCommonInput D data hk a c j hj hkj

/-- Every flat refinement of the entire exact-triple/reciprocal overlap has equal outputs. -/
theorem tripleCommonOutput_reciprocalOverlap {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme) [Flat q]
    (hpq : p ≫ finiteResolvedReciprocalDomainMap hπ data j hj = q ≫ pair) :
    p ≫ finiteResolvedReciprocalAddition hπ data j hj =
      q ≫ tripleCommonOutput D data hk a c j hj hkj := by
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
    exact tripleCommonOutput_reciprocalSecant D data hk a c
      j hj hkj (f ≫ p) (f ≫ q) r hp he
  | true =>
    exact tripleCommonOutput_reciprocalTangent D data hk a c
      j hj hkj (f ≫ p) (f ≫ q) r hp he

end FLT.Mazur.WeierstrassDividedDepth
