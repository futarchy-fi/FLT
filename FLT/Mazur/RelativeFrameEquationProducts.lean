/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameEquationGeometry
public import FLT.Mazur.SchemeAffineEquationIdeal
public import FLT.Mazur.SchemeDisjointClosedIdeals
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Products of full framed endpoint equations

For a closed monic comparison, distinct coordinate equations are disjoint
already on the coefficient test. On affine tests their exact ideals are
comaximal, so the full comparison ideal is the product of the original
coefficient difference ideals. No reduction or radical is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem disjoint_of_maps {X Y Z T : Scheme.{0}}
    (u : X ⟶ Z) (w : Y ⟶ Z) (v : Z ⟶ T) (j : X ⟶ T) (k : Y ⟶ T)
    (hv : Function.Injective v) (hj : u ≫ v = j) (hk : w ≫ v = k)
    (hd : Disjoint (Set.range u) (Set.range w)) :
    Disjoint (Set.range j) (Set.range k) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  have he : u x = w y := hv <| (congrArg (fun t ↦ t x) hj).trans
    (hx.trans (hy.symm.trans (congrArg (fun t ↦ t y) hk).symm))
  exact Set.disjoint_left.mp hd ⟨x, rfl⟩ ⟨y, he.symm⟩

variable {S T Z : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I] {b : T ⟶ S}
  (a : Over.mk b ⟶ distinctScheme E I) (h : E.left ⟶ Z) (y : T ⟶ Z)
local notation "f" => pullback.fst E.hom b ≫ h
local notation "g" => pullback.snd E.hom b ≫ y
local notation "s" i:max => testSection E I a i
local notation "j" i:max => equalizer.ι (s i ≫ f) (s i ≫ g)
local notation "v" => equalizer.ι f g ≫ pullback.snd E.hom b
variable (hv : Function.Injective
  (equalizer.ι (pullback.fst E.hom b ≫ h) (pullback.snd E.hom b ≫ y) ≫ pullback.snd E.hom b))
include hv

omit [Etale E.hom] in
/-- Monicity of the full closed comparison makes coordinate equations disjoint in the test. -/
theorem frameEquation_projection_disjoint (i k : I) (hik : i ≠ k) :
    Disjoint (Set.range (j i)) (Set.range (j k)) :=
  disjoint_of_maps _ _ v (j i) (j k)
    hv
    (frameEquationMap_projection E I a h y i)
    (frameEquationMap_projection E I a h y k)
    (frameEquationMap_disjoint E I a h y i k hik)

variable [IsAffine T] [IsAffine Z]

/-- Each coordinate contributes the ideal of its original endpoint coefficient differences. -/
abbrev frameEquationScalarIdeal (i : I) : Ideal Γ(T, ⊤) :=
  SchemeAffineEquationIdeal.equations (s i ≫ f) (s i ≫ g)

omit [Etale E.hom] in
/-- Distinct coordinate difference ideals are comaximal on the full coefficient ring. -/
theorem frameEquationScalarIdeal_coprime (i k : I) (hik : i ≠ k) :
    IsCoprime (frameEquationScalarIdeal E I a h y i)
      (frameEquationScalarIdeal E I a h y k) := by
  have hc := SchemeDisjointClosedIdeals.kernels_coprime (j i) (j k)
    (frameEquation_projection_disjoint E I a h y hv i k hik)
  simpa only [SchemeAffineEquationIdeal.scalar_kernel_eq] using hc

variable [QuasiCompact
  (equalizer.ι (pullback.fst E.hom b ≫ h) (pullback.snd E.hom b ≫ y) ≫ pullback.snd E.hom b)]

/-- The full comparison kernel is the exact product of its original coordinate equations. -/
theorem frameEquation_scalar_kernel_product (ha : Set.range a.left ⊆ completeLocus E I) :
    RingHom.ker (v).appTop.hom = ∏ i, frameEquationScalarIdeal E I a h y i := by
  have he := congrArg (fun K : T.IdealSheafData ↦ K.ideal ⟨⊤, isAffineOpen_top T⟩)
    (frameEquation_projection_kernel E I a h y ha)
  have hk : RingHom.ker (v).appTop.hom = ⨅ i, RingHom.ker (j i).appTop.hom := by
    simpa only [Scheme.IdealSheafData.ideal_iInf, iInf_apply, Scheme.Hom.ker_apply] using he
  rw [hk, SchemeDisjointClosedIdeals.iInf_kernel_eq_prod _
    (fun _ _ hik ↦ frameEquation_projection_disjoint E I a h y hv _ _ hik)]
  congr 1
  funext i
  exact SchemeAffineEquationIdeal.scalar_kernel_eq _ _

end FLT.Mazur.RelativeOrderedTuples
