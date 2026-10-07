/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicQuadraticDescent
public import FLT.EllipticCurve.CubicBaseChangeCyclic
/-! # Relative quadratic descent for cyclic parameters

The two sign charts prove effective descent after arbitrary scheme base change.
Maps invariant under the pulled-back root involution descend uniquely.
The cyclic coefficient comparison then transfers this descent to the actual
prime cyclic-parameter scheme over the quadratic covering algebra.

The final descent construction requires invariance under the actual covering
involution. Identifying a particular coordinate transport with such an invariant
map is a separate obligation; it is not assumed to follow from root-sign
independence without a coefficient comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (d : Rˣ)
variable {X : Scheme.{u}} (a : X ⟶ Spec (.of R))
/-- The root involution after an arbitrary change of scheme base. -/
def quadraticPullbackSign : pullback a (quadraticEtaleCover d) ⟶
    pullback a (quadraticEtaleCover d) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ quadraticEtaleSignMorphism d) (by
    rw [Category.assoc, quadraticEtaleSignMorphism_over, pullback.condition])
/-- The pulled-back involution fixes the original scheme projection. -/
@[reassoc (attr := simp)]
theorem quadraticPullbackSign_fst :
    quadraticPullbackSign d a ≫ pullback.fst a (quadraticEtaleCover d) =
      pullback.fst a (quadraticEtaleCover d) := pullback.lift_fst _ _ _
/-- The pulled-back involution negates the covering root. -/
@[reassoc (attr := simp)]
theorem quadraticPullbackSign_snd :
    quadraticPullbackSign d a ≫ pullback.snd a (quadraticEtaleCover d) =
      pullback.snd a (quadraticEtaleCover d) ≫ quadraticEtaleSignMorphism d :=
  pullback.lift_snd _ _ _
/-- The pulled-back sign map is an involution. -/
@[reassoc]
theorem quadraticPullbackSign_involutive :
    quadraticPullbackSign d a ≫ quadraticPullbackSign d a = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, quadraticPullbackSign_snd, quadraticPullbackSign_snd_assoc,
      quadraticEtaleSignMorphism_involutive, Category.comp_id, Category.id_comp]
/-- Sign invariance identifies maps above the same base after any base change. -/
theorem quadraticPullbackInvariant_relations (h2 : IsUnit (2 : R)) {Y Z : Scheme.{u}}
    (f : pullback a (quadraticEtaleCover d) ⟶ Y)
    (hf : quadraticPullbackSign d a ≫ f = f)
    (g₁ g₂ : Z ⟶ pullback a (quadraticEtaleCover d))
    (hg : g₁ ≫ pullback.fst _ _ = g₂ ≫ pullback.fst _ _) :
    g₁ ≫ f = g₂ ≫ f := by
  let b₁ := g₁ ≫ pullback.snd a (quadraticEtaleCover d)
  let b₂ := g₂ ≫ pullback.snd a (quadraticEtaleCover d)
  have hb : b₁ ≫ quadraticEtaleCover d = b₂ ≫ quadraticEtaleCover d := by
    dsimp only [b₁, b₂]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hg,
      Category.assoc, pullback.condition, ← Category.assoc]
  let k := pullback.lift b₁ b₂ hb
  let U := quadraticOverlapCover d h2
  apply Scheme.Cover.hom_ext (U.pullback₁ k)
  change ∀ i : Bool, pullback.fst k (quadraticOverlapChartMap d i) ≫ (g₁ ≫ f) =
    pullback.fst k (quadraticOverlapChartMap d i) ≫ (g₂ ≫ f)
  intro i
  let t := pullback.snd k (quadraticOverlapChartMap d i)
  let v := pullback.fst k (quadraticOverlapChartMap d i)
  have ht : t ≫ quadraticOverlapChartMap d i = v ≫ k := pullback.condition.symm
  have h₁ : v ≫ b₁ = t ≫ quadraticOverlapChartMap d i ≫ pullback.fst _ _ := by
    have H := congrArg (fun z => z ≫ pullback.fst (quadraticEtaleCover d)
      (quadraticEtaleCover d)) ht.symm
    simpa only [Category.assoc, k, pullback.lift_fst] using H
  have h₂ : v ≫ b₂ = t ≫ quadraticOverlapChartMap d i ≫ pullback.snd _ _ := by
    have H := congrArg (fun z => z ≫ pullback.snd (quadraticEtaleCover d)
      (quadraticEtaleCover d)) ht.symm
    simpa only [Category.assoc, k, pullback.lift_snd] using H
  change v ≫ (g₁ ≫ f) = v ≫ (g₂ ≫ f)
  cases i
  · have he : v ≫ g₁ = v ≫ g₂ ≫ quadraticPullbackSign d a := by
      apply pullback.hom_ext
      · simp only [Category.assoc, quadraticPullbackSign_fst]
        exact congrArg (fun z => v ≫ z) hg
      · simp only [Category.assoc, quadraticPullbackSign_snd]
        change v ≫ b₁ = (v ≫ b₂) ≫ quadraticEtaleSignMorphism d
        rw [h₁, h₂, quadraticOverlapChartMap_opposite]
        simp only [Category.assoc, quadraticEtaleSignMorphism]
    rw [← Category.assoc, he, Category.assoc, Category.assoc, hf]
  · have he : v ≫ g₁ = v ≫ g₂ := by
      apply pullback.hom_ext
      · simpa only [Category.assoc] using congrArg (fun z => v ≫ z) hg
      · rw [Category.assoc, Category.assoc]
        change v ≫ b₁ = v ≫ b₂
        rw [h₁, h₂, quadraticOverlapChartMap_equal]
    rw [← Category.assoc, he, Category.assoc]

section Relative
variable [Nontrivial R] [Fact (IsUnit (2 : R))]

instance quadraticPullbackCoverEffectiveEpi :
    EffectiveEpi (pullback.fst a (quadraticEtaleCover d)) := by infer_instance

/-- The unique descended map from an arbitrary base-changed quadratic cover. -/
def quadraticPullbackDesc {Y : Scheme.{u}} (f : pullback a (quadraticEtaleCover d) ⟶ Y)
    (hf : quadraticPullbackSign d a ≫ f = f) : X ⟶ Y :=
  EffectiveEpi.desc (pullback.fst a (quadraticEtaleCover d)) f
    (fun g₁ g₂ hg => quadraticPullbackInvariant_relations d a Fact.out f hf g₁ g₂ hg)

/-- Pulling back the descended map recovers the covering map. -/
@[reassoc (attr := simp)]
theorem quadraticPullbackDesc_fac {Y : Scheme.{u}}
    (f : pullback a (quadraticEtaleCover d) ⟶ Y)
    (hf : quadraticPullbackSign d a ≫ f = f) :
    pullback.fst a (quadraticEtaleCover d) ≫ quadraticPullbackDesc d a f hf = f :=
  EffectiveEpi.fac (pullback.fst a (quadraticEtaleCover d)) f
    (fun g₁ g₂ hg => quadraticPullbackInvariant_relations d a Fact.out f hf g₁ g₂ hg)

/-- The descended map is uniquely determined on the covering. -/
theorem quadraticPullbackDesc_unique {Y : Scheme.{u}}
    (f : pullback a (quadraticEtaleCover d) ⟶ Y)
    (hf : quadraticPullbackSign d a ≫ f = f)
    (g : X ⟶ Y) (hg : pullback.fst a (quadraticEtaleCover d) ≫ g = f) :
    g = quadraticPullbackDesc d a f hf := by
  apply (cancel_epi (pullback.fst a (quadraticEtaleCover d))).mp
  rw [quadraticPullbackDesc_fac, hg]

/-- Maps from the base are exactly invariant maps from its pulled-back cover. -/
def quadraticPullbackHomEquiv (Y : Scheme.{u}) :
    (X ⟶ Y) ≃ {f : pullback a (quadraticEtaleCover d) ⟶ Y //
      quadraticPullbackSign d a ≫ f = f} where
  toFun g := ⟨pullback.fst _ _ ≫ g, by rw [← Category.assoc, quadraticPullbackSign_fst]⟩
  invFun f := quadraticPullbackDesc d a f.val f.property
  left_inv g := (quadraticPullbackDesc_unique d a _ _ g rfl).symm
  right_inv f := Subtype.ext (quadraticPullbackDesc_fac d a f.val f.property)


end Relative

section Cyclic
variable [Fact (IsUnit (2 : R))]
variable [IsNoetherianRing R] [IsDomain R]
variable [IsNoetherianRing (QuadraticEtaleRing d)] [IsDomain (QuadraticEtaleRing d)]
variable (W : WeierstrassCurve R) [W.IsElliptic]
variable (p : ℕ) [Fact p.Prime] [Fact (IsUnit (p : R))]
variable [Fact (IsUnit (p : QuadraticEtaleRing d))]

/-- The actual cyclic-parameter scheme identified with the quadratic pullback. -/
def quadraticCyclicPullbackIso :
    (scalarQuotientModel (W.map (algebraMap R (QuadraticEtaleRing d))) p).left ≅
      pullback (scalarQuotientModel W p).hom (quadraticEtaleCover d) :=
  (Over.forget _).mapIso (coefficientScalarQuotientIso W (QuadraticEtaleRing d) p)

omit [Fact (IsUnit (2 : R))] in
/-- The pullback identification projects to the cyclic coefficient map. -/
theorem quadraticCyclicPullbackIso_fst :
    (quadraticCyclicPullbackIso d W p).hom ≫
      pullback.fst (scalarQuotientModel W p).hom (quadraticEtaleCover d) =
        coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p :=
  coefficientScalarQuotientComparison_fst W (QuadraticEtaleRing d) p

instance quadraticCyclicCoverEffectiveEpi :
    EffectiveEpi (coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p) := by
  rw [← quadraticCyclicPullbackIso_fst]
  infer_instance

/-- The covering involution on the actual cyclic-parameter scheme. -/
def quadraticCyclicSign :
    (scalarQuotientModel (W.map (algebraMap R (QuadraticEtaleRing d))) p).left ⟶
      (scalarQuotientModel (W.map (algebraMap R (QuadraticEtaleRing d))) p).left :=
  (quadraticCyclicPullbackIso d W p).hom ≫
    quadraticPullbackSign d (scalarQuotientModel W p).hom ≫
      (quadraticCyclicPullbackIso d W p).inv

omit [Fact (IsUnit (2 : R))] in
/-- The covering involution fixes the original cyclic parameter. -/
theorem quadraticCyclicSign_over :
    quadraticCyclicSign d W p ≫ coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p =
      coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p := by
  rw [quadraticCyclicSign, ← quadraticCyclicPullbackIso_fst]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, quadraticPullbackSign_fst]

omit [Fact (IsUnit (2 : R))] in
/-- The cyclic covering sign map is an involution. -/
theorem quadraticCyclicSign_involutive :
    quadraticCyclicSign d W p ≫ quadraticCyclicSign d W p = 𝟙 _ := by
  simp only [quadraticCyclicSign, Category.assoc, Iso.inv_hom_id_assoc,
    quadraticPullbackSign_involutive_assoc, Iso.hom_inv_id]

omit [Fact (IsUnit (2 : R))] in
/-- Invariance transfers across the cyclic pullback comparison. -/
theorem quadraticCyclicSign_pullback_invariant {Y : Scheme.{u}}
    (f : (scalarQuotientModel (W.map (algebraMap R (QuadraticEtaleRing d))) p).left ⟶ Y)
    (hf : quadraticCyclicSign d W p ≫ f = f) :
    quadraticPullbackSign d (scalarQuotientModel W p).hom ≫
      ((quadraticCyclicPullbackIso d W p).inv ≫ f) =
        (quadraticCyclicPullbackIso d W p).inv ≫ f := by
  simpa only [quadraticCyclicSign, Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun z => (quadraticCyclicPullbackIso d W p).inv ≫ z) hf

/-- Descend an invariant map from the actual cyclic covering. -/
def quadraticCyclicDesc {Y : Scheme.{u}}
    (f : (scalarQuotientModel (W.map (algebraMap R (QuadraticEtaleRing d))) p).left ⟶ Y)
    (hf : quadraticCyclicSign d W p ≫ f = f) :
    (scalarQuotientModel W p).left ⟶ Y :=
  quadraticPullbackDesc d (scalarQuotientModel W p).hom
    ((quadraticCyclicPullbackIso d W p).inv ≫ f)
    (quadraticCyclicSign_pullback_invariant d W p f hf)

/-- Cyclic descent recovers the given map on the quadratic cover. -/
@[reassoc (attr := simp)]
theorem quadraticCyclicDesc_fac {Y : Scheme.{u}}
    (f : (scalarQuotientModel (W.map (algebraMap R (QuadraticEtaleRing d))) p).left ⟶ Y)
    (hf : quadraticCyclicSign d W p ≫ f = f) :
    coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p ≫
      quadraticCyclicDesc d W p f hf = f := by
  rw [← quadraticCyclicPullbackIso_fst, Category.assoc, quadraticCyclicDesc,
    quadraticPullbackDesc_fac, Iso.hom_inv_id_assoc]

/-- Cyclic descent is unique. -/
theorem quadraticCyclicDesc_unique {Y : Scheme.{u}}
    (f : (scalarQuotientModel (W.map (algebraMap R (QuadraticEtaleRing d))) p).left ⟶ Y)
    (hf : quadraticCyclicSign d W p ≫ f = f)
    (g : (scalarQuotientModel W p).left ⟶ Y)
    (hg : coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p ≫ g = f) :
    g = quadraticCyclicDesc d W p f hf := by
  apply (cancel_epi (coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p)).mp
  rw [quadraticCyclicDesc_fac, hg]

end Cyclic

end WeierstrassCurve.CubicCharts
