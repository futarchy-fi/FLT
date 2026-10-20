/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentFlatSourceExt
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing actual smooth tangent outputs on open source domains

Agreement of cubic contractions implies agreement of the constructed
resolved outputs on every overlap: these overlaps are flat over the
original source. Consequently the outputs glue on their entire open union.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n k : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  {m : ℕ} (d : Data W π m)
  (a c : Coordinate W (π ^ m) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ m
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "U" => (finiteGlobalStructure hπ data k hk).smoothLocus
local notation "sec" => dividedTangentToCurve W s d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6
variable {I : Type u}
  (O : I → (Spec (.of (DividedTangentRing W (π ^ m) d.b3 d.b4 d.b6 a c))).Opens)
  (v : (i : I) → (O i).toScheme ⟶ (finiteGlobalStructure hπ data k hk).smoothLocus.toScheme)
  (hv : ∀ i, v i ≫ (finiteGlobalStructure hπ data k hk).smoothLocus.ι ≫
    finiteGlobalContraction hπ data k hk = (O i).ι ≫
      dividedTangentToCurve W (π ^ m) d.b3 d.b4 d.b6 a c
        d.factor3 d.factor4 d.factor6)
local notation "C" => Scheme.Opens.iSupOpenCover O
local notation "V" => ⨆ i, O i

include hv in
/-- Regular-scale uniqueness proves resolved output compatibility on the entire overlaps. -/
theorem finiteTangentOpenOutput_compatible (i j : I) :
    pullback.fst ((C).f i) ((C).f j) ≫ v i =
      pullback.snd ((C).f i) ((C).f j) ≫ v j := by
  have hi : (C).f i ≫ (V).ι = (O i).ι := Scheme.homOfLE_ι _ (le_iSup O i)
  have hj : (C).f j ≫ (V).ι = (O j).ι := Scheme.homOfLE_ι _ (le_iSup O j)
  have hp : pullback.fst ((C).f i) ((C).f j) ≫ (O i).ι =
      pullback.snd ((C).f i) ((C).f j) ≫ (O j).ι := by
    simpa only [Category.assoc, hi, hj] using
      congrArg (fun z => z ≫ (V).ι) (pullback.condition (f := (C).f i) (g := (C).f j))
  apply (cancel_mono (U).ι).mp
  apply finiteTangentOutput_ext hπ data hk d a c
    (pullback.fst ((C).f i) ((C).f j) ≫ (O i).ι)
  · simp only [Category.assoc, hv]
  · simp only [Category.assoc, hv]
    exact congrArg (fun z => z ≫ sec) hp.symm

/-- Glue the actual local outputs into the same finite-model smooth locus. -/
def finiteTangentOpenOutput : (V).toScheme ⟶ (U).toScheme :=
  (C).glueMorphisms v (finiteTangentOpenOutput_compatible hπ data hk d a c O v hv)

/-- Gluing recovers the specified output on each whole input open. -/
@[reassoc] theorem finiteTangentOpenOutput_restrict (i : I) :
    (C).f i ≫ finiteTangentOpenOutput hπ data hk d a c O v hv = v i :=
  (C).ι_glueMorphisms v (finiteTangentOpenOutput_compatible hπ data hk d a c O v hv) i

/-- The glued output retains the original tangent contraction everywhere on the union. -/
@[reassoc] theorem finiteTangentOpenOutput_contraction :
    finiteTangentOpenOutput hπ data hk d a c O v hv ≫ (U).ι ≫
        finiteGlobalContraction hπ data k hk = (V).ι ≫ sec := by
  apply (C).hom_ext
  intro i
  rw [finiteTangentOpenOutput_restrict_assoc, hv]
  have hi : (C).f i ≫ (V).ι = (O i).ι := Scheme.homOfLE_ι _ (le_iSup O i)
  rw [← Category.assoc, hi]

end FLT.Mazur.WeierstrassDividedDepth
