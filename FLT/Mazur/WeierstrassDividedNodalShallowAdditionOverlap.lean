/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalShallowAdditionSource
public import FLT.Mazur.WeierstrassDividedReindexedTangentSecantExt

/-!
# Full-overlap compatibility of shallow tangent and secant outputs

The two original formulas agree over their common input source. Their
resolved outputs agree by flat-source uniqueness, even over the original
singular point. No restriction to an originally smooth output is used.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
  nodalShallowBranchCommonOutput nodalShallowNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 2 * k ≤ m) (hm : m ≤ 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : m - 2 * k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "V" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "v" => Spec.map (CommRingCat.ofHom (algebraMap S V))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (start := 0) data (m - 2 * k) hj
local notation "U" => (base).smoothLocus
local notation "Ot" => nodalShallowTangentBranchOutputOpen D hdepth hm data hj d a c
local notation "Os" => ⨆ i, nodalShallowSecantLocalOpen D hdepth hm data hj d a c i
local notation "ft" => nodalShallowTangentGluedOutput D hdepth hm data hj d a c
local notation "fs" => nodalShallowSecantGluedOutput D hdepth hm data hj d a c

local notation "src" => nodalShallowAdditionSource D hdepth hm data hj d a c
local notation "inc" => nodalShallowAdditionInclusion D hdepth hm data hj d a c
local notation "out" => nodalShallowAdditionOutput D hdepth hm data hj d a c
local notation "tan" => dividedTangentToCurve W s d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6
local notation "sec" => dividedSecantToCurve W s d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6

/-- Actual outputs agree on every common flat refinement of their original input domains. -/
theorem nodalShallowAdditionOutput_overlap (i j : Bool) {X : Scheme}
    (p : X ⟶ src i) (q : X ⟶ src j) [Flat p] [Flat q]
    (hpq : p ≫ inc i = q ≫ inc j) : p ≫ out i = q ≫ out j := by
  let _ : IsOpenImmersion t :=
    IsOpenImmersion.of_isLocalization (dividedTangentDenominator W s d.b3 d.b4 d.b6 a c)
  let _ : IsOpenImmersion v :=
    IsOpenImmersion.of_isLocalization (a (x W s d.b3 d.b4 d.b6) - c (x W s d.b3 d.b4 d.b6))
  apply (cancel_mono (U).ι).mp
  cases i <;> cases j
  · have he : p ≫ (Os).ι = q ≫ (Os).ι := (cancel_mono v).mp
      (by simpa only [nodalShallowAdditionInclusion, Category.assoc] using hpq)
    apply finiteReindexedSecantOutput_ext hπ (start := 0) data hj d a c (p ≫ (Os).ι)
    · simp only [nodalShallowAdditionOutput, Category.assoc,
        nodalShallowSecantGluedOutput_contraction]
    · simp only [nodalShallowAdditionOutput, Category.assoc,
        nodalShallowSecantGluedOutput_contraction]
      exact congrArg (fun z => z ≫ sec) he.symm
  · symm
    apply finiteReindexedTangentSecantOutput_ext hπ (start := 0) data hj d a c
      (q ≫ (Ot).ι) (p ≫ (Os).ι)
      (by simpa only [nodalShallowAdditionInclusion, Category.assoc] using hpq.symm)
    · simp only [nodalShallowAdditionOutput, Category.assoc,
        nodalShallowTangentGluedOutput_contraction]
    · simp only [nodalShallowAdditionOutput, Category.assoc,
        nodalShallowSecantGluedOutput_contraction]
  · apply finiteReindexedTangentSecantOutput_ext hπ (start := 0) data hj d a c
      (p ≫ (Ot).ι) (q ≫ (Os).ι)
      (by simpa only [nodalShallowAdditionInclusion, Category.assoc] using hpq)
    · simp only [nodalShallowAdditionOutput, Category.assoc,
        nodalShallowTangentGluedOutput_contraction]
    · simp only [nodalShallowAdditionOutput, Category.assoc,
        nodalShallowSecantGluedOutput_contraction]
  · have he : p ≫ (Ot).ι = q ≫ (Ot).ι := (cancel_mono t).mp
      (by simpa only [nodalShallowAdditionInclusion, Category.assoc] using hpq)
    apply finiteTangentOutput_ext hπ (start := 0) data hj d a c (p ≫ (Ot).ι)
    · simp only [nodalShallowAdditionOutput, Category.assoc,
        nodalShallowTangentGluedOutput_contraction]
    · simp only [nodalShallowAdditionOutput, Category.assoc,
        nodalShallowTangentGluedOutput_contraction]
      exact congrArg (fun z => z ≫ tan) he.symm

end FLT.Mazur.WeierstrassDividedDepth
