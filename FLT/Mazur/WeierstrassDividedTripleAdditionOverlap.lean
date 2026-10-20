/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleAdditionSource
public import FLT.Mazur.WeierstrassDividedReindexedTangentSecantExt
public import FLT.Mazur.WeierstrassDividedReindexedSecantFlatSourceExt

/-!
# Full-overlap compatibility of exact-triple tangent and secant outputs

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
  tripleBranchCommonOutput tripleNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "s" => π ^ (start + k)
local notation "T" => DividedTangentRing W s (d).b3 (d).b4 (d).b6 a c
local notation "V" => DividedSecantRing W s (d).b3 (d).b4 (d).b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "v" => Spec.map (CommRingCat.ofHom (algebraMap S V))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus
local notation "Ot" => tripleTangentBranchOutputOpen D data hk a c
local notation "Os" => ⨆ i, tripleSecantLocalOpen D data hk a c i
local notation "ft" => tripleTangentGluedOutput D data hk a c
local notation "fs" => tripleSecantGluedOutput D data hk a c

local notation "src" => tripleAdditionSource D data hk a c
local notation "inc" => tripleAdditionInclusion D data hk a c
local notation "out" => tripleAdditionOutput D data hk a c
local notation "tan" => dividedTangentToCurve W s (d).b3 (d).b4 (d).b6 a c
  (d).factor3 (d).factor4 (d).factor6
local notation "sec" => dividedSecantToCurve W s (d).b3 (d).b4 (d).b6 a c
  (d).factor3 (d).factor4 (d).factor6

/-- Actual outputs agree on every common flat refinement of their original input domains. -/
theorem tripleAdditionOutput_overlap (i j : Bool) {X : Scheme}
    (p : X ⟶ src i) (q : X ⟶ src j) [Flat p] [Flat q]
    (hpq : p ≫ inc i = q ≫ inc j) : p ≫ out i = q ≫ out j := by
  let _ : IsOpenImmersion t :=
    IsOpenImmersion.of_isLocalization (dividedTangentDenominator W s (d).b3 (d).b4 (d).b6 a c)
  let _ : IsOpenImmersion v :=
    IsOpenImmersion.of_isLocalization
      (a (x W s (d).b3 (d).b4 (d).b6) - c (x W s (d).b3 (d).b4 (d).b6))
  apply (cancel_mono (U).ι).mp
  cases i <;> cases j
  · have he : p ≫ (Os).ι = q ≫ (Os).ι := (cancel_mono v).mp
      (by simpa only [tripleAdditionInclusion, Category.assoc] using hpq)
    apply finiteReindexedSecantOutput_ext hπ data hk d a c (p ≫ (Os).ι)
    · simp only [tripleAdditionOutput, Category.assoc,
        tripleSecantGluedOutput_contraction]
    · simp only [tripleAdditionOutput, Category.assoc,
        tripleSecantGluedOutput_contraction]
      exact congrArg (fun z => z ≫ sec) he.symm
  · symm
    apply finiteReindexedTangentSecantOutput_ext hπ data hk d a c
      (q ≫ (Ot).ι) (p ≫ (Os).ι)
      (by simpa only [tripleAdditionInclusion, Category.assoc] using hpq.symm)
    · simp only [tripleAdditionOutput, Category.assoc,
        tripleTangentGluedOutput_contraction]
    · simp only [tripleAdditionOutput, Category.assoc,
        tripleSecantGluedOutput_contraction]
  · apply finiteReindexedTangentSecantOutput_ext hπ data hk d a c
      (p ≫ (Ot).ι) (q ≫ (Os).ι)
      (by simpa only [tripleAdditionInclusion, Category.assoc] using hpq)
    · simp only [tripleAdditionOutput, Category.assoc,
        tripleTangentGluedOutput_contraction]
    · simp only [tripleAdditionOutput, Category.assoc,
        tripleSecantGluedOutput_contraction]
  · have he : p ≫ (Ot).ι = q ≫ (Ot).ι := (cancel_mono t).mp
      (by simpa only [tripleAdditionInclusion, Category.assoc] using hpq)
    apply finiteTangentOutput_ext hπ data hk d a c (p ≫ (Ot).ι)
    · simp only [tripleAdditionOutput, Category.assoc,
        tripleTangentGluedOutput_contraction]
    · simp only [tripleAdditionOutput, Category.assoc,
        tripleTangentGluedOutput_contraction]
      exact congrArg (fun z => z ≫ tan) he.symm

end FLT.Mazur.WeierstrassDividedDepth
