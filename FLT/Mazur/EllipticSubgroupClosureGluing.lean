/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupOverlapLocalization
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Gluing integral subgroup chart closures

Glue two actual kernel-quotient chart closures along their principal opens,
using the proved coordinate transition. The resulting scheme is covered by
the two closure charts and has a canonical morphism to the valuation ring.
For the Weierstrass Y/Z cover take j = 1 and k = 2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.EllipticSubgroupChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j k : Fin 3)

/-- The affine subgroup closure in one homogeneous chart. -/
abbrev closureChart := Spec (.of (Closure A W H j))

/-- The common principal open, presented in the first chart. -/
abbrev closureIntersection := Spec (.of (LocalizedClosure A W H j k))

/-- The overlap change as an isomorphism of affine schemes. -/
def closureIntersectionIso : closureIntersection A W H j k ≅ closureIntersection A W H k j :=
  Scheme.Spec.mapIso (localizedClosureEquiv A W H j k).toRingEquiv.toCommRingCatIso.op

/-- The canonical principal open immersion into the first closure chart. -/
def closureToLeft : closureIntersection A W H j k ⟶ closureChart A W H j :=
  Spec.map (CommRingCat.ofHom (algebraMap (Closure A W H j) (LocalizedClosure A W H j k)))

instance : IsOpenImmersion (closureToLeft A W H j k) := by
  dsimp [closureToLeft]
  infer_instance

/-- The principal open immersion into the second closure chart after renormalization. -/
def closureToRight : closureIntersection A W H j k ⟶ closureChart A W H k :=
  (closureIntersectionIso A W H j k).hom ≫ closureToLeft A W H k j

instance : IsOpenImmersion (closureToRight A W H j k) := by
  dsimp [closureToRight]
  infer_instance

/-- The scheme obtained by gluing the actual subgroup closure charts. -/
def gluedClosure : Scheme := pushout (closureToLeft A W H j k) (closureToRight A W H j k)

/-- Inclusion of the first affine closure chart. -/
def closureLeft : closureChart A W H j ⟶ gluedClosure A W H j k := pushout.inl _ _

/-- Inclusion of the second affine closure chart. -/
def closureRight : closureChart A W H k ⟶ gluedClosure A W H j k := pushout.inr _ _

instance : IsOpenImmersion (closureLeft A W H j k) := by
  change IsOpenImmersion
    (colimit.ι (span (closureToLeft A W H j k) (closureToRight A W H j k)) WalkingSpan.left)
  infer_instance

instance : IsOpenImmersion (closureRight A W H j k) := by
  change IsOpenImmersion
    (colimit.ι (span (closureToLeft A W H j k) (closureToRight A W H j k)) WalkingSpan.right)
  infer_instance

/-- The two inclusions agree on the subgroup closure overlap. -/
theorem closure_overlap_condition :
    closureToLeft A W H j k ≫ closureLeft A W H j k =
      closureToRight A W H j k ≫ closureRight A W H j k := pushout.condition

/-- Every point of the glued closure belongs to one of its two affine charts. -/
theorem closure_charts_cover (x : gluedClosure A W H j k) :
    (∃ y : closureChart A W H j, closureLeft A W H j k y = x) ∨
      ∃ y : closureChart A W H k, closureRight A W H j k y = x := by
  obtain ⟨i, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (closureToLeft A W H j k) (closureToRight A W H j k)) x
  cases i with
  | none =>
    left
    refine ⟨closureToLeft A W H j k y, ?_⟩
    change (closureToLeft A W H j k ≫ closureLeft A W H j k) y = x
    rw [show closureToLeft A W H j k ≫ closureLeft A W H j k =
      colimit.ι (span (closureToLeft A W H j k) (closureToRight A W H j k))
        WalkingSpan.zero from colimit.w
          (span (closureToLeft A W H j k) (closureToRight A W H j k)) WalkingSpan.Hom.fst]
    exact hy
  | some i =>
    cases i with
    | left => exact Or.inl ⟨y, hy⟩
    | right => exact Or.inr ⟨y, hy⟩

/-- The natural structural morphism on each affine chart. -/
def closureChartToBase : closureChart A W H j ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Closure A W H j)))

set_option backward.isDefEq.respectTransparency false in
/-- Both overlap immersions preserve the valuation-ring coefficients. -/
theorem closure_overlap_toBase :
    closureToLeft A W H j k ≫ closureChartToBase A W H j =
      closureToRight A W H j k ≫ closureChartToBase A W H k := by
  have h : (algebraMap (Closure A W H j) (LocalizedClosure A W H j k)).comp
      (algebraMap A (Closure A W H j)) =
      (localizedClosureEquiv A W H j k).toRingHom.comp
        ((algebraMap (Closure A W H k) (LocalizedClosure A W H k j)).comp
          (algebraMap A (Closure A W H k))) := by
    ext a
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    exact ((localizedClosureEquiv A W H j k).commutes a).symm
  simpa only [closureToLeft, closureChartToBase, closureToRight, closureIntersectionIso,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Functor.mapIso_hom,
    Iso.op_hom, RingEquiv.toCommRingCatIso_hom, Scheme.Spec_map,
    Quiver.Hom.unop_op, RingEquiv.toRingHom_eq_coe] using
    congrArg (fun f : A →+* LocalizedClosure A W H j k => Spec.map (CommRingCat.ofHom f)) h

/-- The glued subgroup closure as a scheme over the valuation ring. -/
def closureToBase : gluedClosure A W H j k ⟶ Spec (.of A) :=
  pushout.desc (closureChartToBase A W H j) (closureChartToBase A W H k)
    (closure_overlap_toBase A W H j k)

/-- The structural map restricts to the first chart's structural map. -/
@[reassoc (attr := simp)] theorem closureLeft_toBase :
    closureLeft A W H j k ≫ closureToBase A W H j k = closureChartToBase A W H j :=
  pushout.inl_desc _ _ _

/-- The structural map restricts to the second chart's structural map. -/
@[reassoc (attr := simp)] theorem closureRight_toBase :
    closureRight A W H j k ≫ closureToBase A W H j k = closureChartToBase A W H k :=
  pushout.inr_desc _ _ _

end FLT.Mazur.EllipticSubgroupChart
