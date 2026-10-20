/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiveRegimeAmbientAddition
public import FLT.Mazur.WeierstrassDividedSmoothFamilyComparison

/-!
# Transport the entire five-regime law to a differently indexed family

The supplied family may have any length containing the doubled stage. The
proved comparison of finite constructions transports the actual union law,
its whole four-regime and quadruple restrictions, and its coefficient maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure rootShearCurve
  nodalSecondShear nodalSecondQuotient
variable {R : Type} [CommRing R] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (D : SplitNodeDepth W π (4 * k)) (d : Data W π k)
local notation "data" => splitNodeDoubledFamily D
local notation "j" => k + k
local notation "hj" => (le_rfl : k + k ≤ k + k)
local notation "a" => dividedPairLeft W (π ^ k) (d).b3 (d).b4 (d).b6
local notation "c" => dividedPairRight W (π ^ k) (d).b3 (d).b4 (d).b6
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => nodalQuadrupleAdditionOpen D d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

local notation "V" => quadrupleSmoothSourceOpen D d a c
local notation "pair" => quadrupleCommonInput D d a c
local notation "Old" => finiteResolvedReciprocalExtendedOpen hπ data j hj

variable {q i r l v : ℕ} (D' : SplitNodeDepth W π (3 * (0 + q)))
  (hi : 3 * i ≤ 3 * (0 + q)) (hri : r ≤ i) (hrm : r ≤ 3 * (0 + q) - 3 * i)
  (hir : i + r ≤ k + k) (di : Data W π i) (hij : i ≤ k + k)
  (hs : 2 * l ≤ 3 * (0 + q)) (hsm : 3 * (0 + q) ≤ 3 * l)
  (hsn : 3 * (0 + q) - 2 * l ≤ k + k) (dl : Data W π l) (hlj : l ≤ k + k)
  (hq : q ≤ k + k) (hv : v + v ≤ k + k) (dv : Data W π v)
local notation "Three" => threeRegimeAmbientOpen D' hi hri hrm data hir di
  j hj hij hs hsm hsn dl hlj hq hq
local notation "fthree" => threeRegimeAmbientAddition D' hi hri hrm data hir di
  j hj hij hir hs hsm hsn dl hlj hsn hq hq
local notation "incThree" => threeRegimeAmbientInput D' hi hri hrm data hir di
  j hj hij hs hsm hsn dl hlj hq hq
local notation "outThree" => threeRegimeAmbientLocal D' hi hri hrm data hir di
  j hj hij hir hs hsm hsn dl hlj hsn hq hq
local notation "Four" => fourRegimeAmbientOpen D' hi hri hrm data hir di
  j hj hij hs hsm hsn dl hlj hq hq hv dv hv
local notation "ffour" => fourRegimeAmbientAddition D' hi hri hrm data hir di
  j hj hij hir hs hsm hsn dl hlj hsn hq hq hv dv hv
local notation "incFour" => fourRegimeAmbientInput D' hi hri hrm data hir di
  j hj hij hs hsm hsn dl hlj hq hq hv dv hv
local notation "outFour" => fourRegimeAmbientLocal D' hi hri hrm data hir di
  j hj hij hir hs hsm hsn dl hlj hsn hq hq hv dv hv
local notation "Quad" => quadrupleAmbientOpen D d
local notation "fquad" => quadrupleAmbientAddition D d

local notation "Union" => fiveRegimeAmbientOpen D d D' hi hri hrm hir di hij
  hs hsm hsn dl hlj hq hv dv
local notation "law" => fiveRegimeAmbientAddition D d D' hi hri hrm hir di hij
  hs hsm hsn dl hlj hq hv dv
local notation "inc" => fiveRegimeAmbientInput D d D' hi hri hrm hir di hij
  hs hsm hsn dl hlj hq hv dv

variable {n : ℕ} (supplied : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (hn : k + k ≤ n)
local notation "base'" => finiteGlobalStructure hπ supplied j hn
local notation "U'" => (base').smoothLocus
local notation "t'" => (U').ι ≫ base'
local notation "eP" => eqToHom (finiteResolvedProduct_family_eq hπ data supplied j hj hn)
local notation "eU" => eqToHom (finiteSmoothScheme_family_eq hπ data supplied j hj hn)

/-- The whole constructed union embedded in the supplied ambient product. -/
def fiveReindexedAmbientInput :
    (Union).toScheme ⟶ finiteResolvedProduct hπ supplied j hn := (Union).ι ≫ eP

local notation "input" => fiveReindexedAmbientInput D d D' hi hri hrm hir di hij
  hs hsm hsn dl hlj hq hv dv supplied hn

instance fiveReindexedAmbientInput_open : IsOpenImmersion input := by
  dsimp only [fiveReindexedAmbientInput]
  infer_instance

/-- The actual image of the entire five-regime domain in the supplied product. -/
def fiveReindexedAmbientOpen : (finiteResolvedProduct hπ supplied j hn).Opens :=
  (input).opensRange

local notation "New" => fiveReindexedAmbientOpen D d D' hi hri hrm hir di hij
  hs hsm hsn dl hlj hq hv dv supplied hn

/-- The transported law uses the whole old domain and the proved smooth identification. -/
def fiveReindexedAmbientAddition : (New).toScheme ⟶ (U').toScheme :=
  (input).isoOpensRange.inv ≫ law ≫ eU

local notation "newLaw" => fiveReindexedAmbientAddition D d D' hi hri hrm hir di hij
  hs hsm hsn dl hlj hq hv dv supplied hn

/-- The original whole five-regime law is retained by the transport. -/
@[reassoc] theorem fiveReindexedAmbientAddition_whole :
    (input).isoOpensRange.hom ≫ newLaw = law ≫ eU := by
  dsimp only [fiveReindexedAmbientAddition]
  rw [Iso.hom_inv_id_assoc]

/-- The transported domain is precisely the image of the existing union. -/
theorem fiveReindexedAmbientOpen_eq : New = eP ''ᵁ Union := by
  change ((Union).ι ≫ eP).opensRange = _
  exact (Scheme.Hom.opensRange_comp (Union).ι eP).trans
    (congrArg (fun Ω => eP ''ᵁ Ω) (Scheme.Opens.opensRange_ι Union))

/-- The whole four-regime restriction survives in the differently indexed family. -/
@[reassoc] theorem fiveReindexedAmbientAddition_four :
    (openImageUnionMap inc false ≫ (input).isoOpensRange.hom) ≫ newLaw = ffour ≫ eU := by
  rw [Category.assoc, fiveReindexedAmbientAddition_whole,
    fiveRegimeAmbientAddition_four_assoc]

/-- The whole quadruple restriction survives in the differently indexed family. -/
@[reassoc] theorem fiveReindexedAmbientAddition_quadruple :
    (openImageUnionMap inc true ≫ (input).isoOpensRange.hom) ≫ newLaw = fquad ≫ eU := by
  rw [Category.assoc, fiveReindexedAmbientAddition_whole,
    fiveRegimeAmbientAddition_quadruple_assoc]

/-- The first input's original coefficient point is retained. -/
@[reassoc] theorem fiveReindexedAmbientAddition_structure :
    newLaw ≫ t' = (New).ι ≫ pullback.fst t' t' ≫ t' := by
  apply (cancel_epi (input).isoOpensRange.hom).mp
  rw [fiveReindexedAmbientAddition_whole_assoc,
    finiteSmoothScheme_family_structure, fiveRegimeAmbientAddition_structure]
  dsimp only [fiveReindexedAmbientOpen]
  rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]
  dsimp only [fiveReindexedAmbientInput]
  rw [Category.assoc, finiteResolvedProduct_family_structure]

/-- The second input has the same retained coefficient point. -/
@[reassoc] theorem fiveReindexedAmbientAddition_structure_snd :
    newLaw ≫ t' = (New).ι ≫ pullback.snd t' t' ≫ t' := by
  rw [fiveReindexedAmbientAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
