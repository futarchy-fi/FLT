/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicTransportFunctor
public import FLT.EllipticCurve.CubicCyclicGroup

/-! # Effective descent through the prime scalar quotient

The graphs of scalar multiplication form an open cover of the kernel pair
of the generator-forgetting map. A scalar-invariant morphism to any scheme
therefore coequalizes this kernel pair and descends uniquely.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
variable (W : WeierstrassCurve R) [W.IsElliptic]
variable (p : ℕ) [Fact p.Prime] [NeZero p] [Fact (IsUnit (p : R))]

/-- The kernel pair of the map forgetting a prime generator. -/
def scalarRelation : Scheme :=
  pullback (scalarQuotientMap W p).left (scalarQuotientMap W p).left

/-- The graph of scalar multiplication in the generator relation scheme. -/
def scalarRelationChart (a : (ZMod p)ˣ) :
    (nonzeroTorsionModel W p).left ⟶ scalarRelation W p :=
  pullback.lift (𝟙 _) (nonzeroTorsionScalarAction W p a).hom.left (by
    rw [Category.id_comp]
    exact (congrArg Over.Hom.left (scalarQuotientMap_invariant W p a)).symm)

/-- Each scalar graph is an open subscheme of the relation scheme. -/
theorem scalarRelationChart_open (a : (ZMod p)ˣ) :
    IsOpenImmersion (scalarRelationChart W p a) := by
  have := scalarQuotientMap_etale W p
  have : Etale (scalarRelationChart W p a ≫
      pullback.fst (scalarQuotientMap W p).left (scalarQuotientMap W p).left) := by
    simp only [scalarRelationChart, pullback.lift_fst]
    infer_instance
  have : Mono (scalarRelationChart W p a) :=
    mono_of_mono_fac (show scalarRelationChart W p a ≫
      pullback.fst _ _ = 𝟙 _ from pullback.lift_fst _ _ _)
  have := Etale.of_comp (scalarRelationChart W p a) (pullback.fst _ _)
  exact IsOpenImmersion.of_flat_of_mono _

/-- The generator relation scheme over the coefficient base. -/
def scalarRelationModel : Over (Spec (.of R)) :=
  Over.mk (pullback.fst (scalarQuotientMap W p).left (scalarQuotientMap W p).left ≫
    (nonzeroTorsionModel W p).hom)

/-- The first generator in a relation. -/
def scalarRelationFirst : scalarRelationModel W p ⟶ nonzeroTorsionModel W p :=
  Over.homMk (pullback.fst _ _) rfl

/-- The second generator in a relation. -/
def scalarRelationSecond : scalarRelationModel W p ⟶ nonzeroTorsionModel W p :=
  Over.homMk (pullback.snd (scalarQuotientMap W p).left (scalarQuotientMap W p).left) (by
    rw [← (scalarQuotientMap W p).w, ← Category.assoc, ← pullback.condition,
      Category.assoc, (scalarQuotientMap W p).w]
    rfl)

omit [Fact p.Prime] in
/-- Related generators have the same cyclic parameter. -/
theorem scalarRelation_projections :
    scalarRelationFirst W p ≫ scalarQuotientMap W p =
      scalarRelationSecond W p ≫ scalarQuotientMap W p := by
  apply Over.OverMorphism.ext
  exact pullback.condition

/-- Every relation lies in a scalar graph. -/
theorem scalarRelationChart_cover :
    ∀ x : scalarRelation W p, ∃ a : (ZMod p)ˣ, x ∈ Set.range (scalarRelationChart W p a) := by
  apply over_geometricPoints_cover (scalarRelationModel W p)
    {x | ∃ a : (ZMod p)ˣ, x ∈ Set.range (scalarRelationChart W p a)}
  intro K _ _ _ t y hy
  obtain ⟨z, rfl⟩ := hy
  let x₁ := t ≫ scalarRelationFirst W p
  let x₂ := t ≫ scalarRelationSecond W p
  have hq : x₂ ≫ scalarQuotientMap W p = x₁ ≫ scalarQuotientMap W p := by
    dsimp only [x₁, x₂]
    rw [Category.assoc, Category.assoc, scalarRelation_projections]
  obtain ⟨a, ha⟩ := (scalarQuotientFieldPoint_fiber_hom W p K x₂ x₁).mp hq
  have ht : t.left = x₁.left ≫ scalarRelationChart W p a := by
    apply pullback.hom_ext
    · simp only [Category.assoc, scalarRelationChart, pullback.lift_fst, Category.comp_id]
      rfl
    · simp only [Category.assoc, scalarRelationChart, pullback.lift_snd]
      exact congrArg Over.Hom.left ha
  refine ⟨a, x₁.left z, ?_⟩
  rw [ht]
  rfl

/-- The open cover of generator relations by scalar graphs. -/
def scalarRelationCover : (scalarRelation W p).OpenCover where
  I₀ := (ZMod p)ˣ
  X _ := (nonzeroTorsionModel W p).left
  f := scalarRelationChart W p
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨scalarRelationChart_cover W p, fun a => scalarRelationChart_open W p a⟩


/-- A scalar-invariant morphism coequalizes the kernel-pair projections. -/
theorem scalarInvariantMap_relation {X : Scheme.{u}}
    (f : (nonzeroTorsionModel W p).left ⟶ X)
    (hf : ∀ a : (ZMod p)ˣ, (nonzeroTorsionScalarAction W p a).hom.left ≫ f = f) :
    pullback.fst (scalarQuotientMap W p).left (scalarQuotientMap W p).left ≫ f =
      pullback.snd (scalarQuotientMap W p).left (scalarQuotientMap W p).left ≫ f := by
  apply (scalarRelationCover W p).hom_ext
  intro a
  change scalarRelationChart W p a ≫ _ = scalarRelationChart W p a ≫ _
  simp only [← Category.assoc, scalarRelationChart, pullback.lift_fst, pullback.lift_snd,
    Category.id_comp, hf]

/-- Scalar invariance identifies every pair of maps with the same cyclic parameter. -/
theorem scalarInvariantMap_relations {X Z : Scheme.{u}}
    (f : (nonzeroTorsionModel W p).left ⟶ X)
    (hf : ∀ a : (ZMod p)ˣ, (nonzeroTorsionScalarAction W p a).hom.left ≫ f = f)
    (g₁ g₂ : Z ⟶ (nonzeroTorsionModel W p).left)
    (h : g₁ ≫ (scalarQuotientMap W p).left = g₂ ≫ (scalarQuotientMap W p).left) :
    g₁ ≫ f = g₂ ≫ f := by
  have ht := congrArg (fun k => pullback.lift g₁ g₂ h ≫ k)
    (scalarInvariantMap_relation W p f hf)
  simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using ht

/-- The morphism descended from a scalar-invariant morphism to any scheme. -/
def scalarQuotientDesc {X : Scheme.{u}}
    (f : (nonzeroTorsionModel W p).left ⟶ X)
    (hf : ∀ a : (ZMod p)ˣ, (nonzeroTorsionScalarAction W p a).hom.left ≫ f = f) :
    (scalarQuotientModel W p).left ⟶ X :=
  EffectiveEpi.desc (scalarQuotientMap W p).left f
    (fun g₁ g₂ h => scalarInvariantMap_relations W p f hf g₁ g₂ h)

/-- The descended map recovers the given map on generators. -/
@[reassoc (attr := simp)]
theorem scalarQuotientDesc_fac {X : Scheme.{u}}
    (f : (nonzeroTorsionModel W p).left ⟶ X)
    (hf : ∀ a : (ZMod p)ˣ, (nonzeroTorsionScalarAction W p a).hom.left ≫ f = f) :
    (scalarQuotientMap W p).left ≫ scalarQuotientDesc W p f hf = f :=
  EffectiveEpi.fac _ _ _

/-- Descent from generators is unique. -/
theorem scalarQuotientDesc_unique {X : Scheme.{u}}
    (f : (nonzeroTorsionModel W p).left ⟶ X)
    (hf : ∀ a : (ZMod p)ˣ, (nonzeroTorsionScalarAction W p a).hom.left ≫ f = f)
    (g : (scalarQuotientModel W p).left ⟶ X)
    (hg : (scalarQuotientMap W p).left ≫ g = f) :
    g = scalarQuotientDesc W p f hf := by
  apply (cancel_epi (scalarQuotientMap W p).left).mp
  rw [scalarQuotientDesc_fac, hg]

/-- Every morphism from cyclic parameters is invariant on generators. -/
theorem scalarQuotientComposite_invariant {X : Scheme.{u}}
    (g : (scalarQuotientModel W p).left ⟶ X) (a : (ZMod p)ˣ) :
    (nonzeroTorsionScalarAction W p a).hom.left ≫ (scalarQuotientMap W p).left ≫ g =
      (scalarQuotientMap W p).left ≫ g := by
  rw [← Category.assoc]
  exact congrArg (fun f => f ≫ g)
    (congrArg Over.Hom.left (scalarQuotientMap_invariant W p a))

/-- The categorical quotient property for maps to an arbitrary scheme. -/
def scalarQuotientHomEquiv (X : Scheme.{u}) :
    ((scalarQuotientModel W p).left ⟶ X) ≃
      {f : (nonzeroTorsionModel W p).left ⟶ X //
        ∀ a : (ZMod p)ˣ, (nonzeroTorsionScalarAction W p a).hom.left ≫ f = f} where
  toFun g := ⟨(scalarQuotientMap W p).left ≫ g, scalarQuotientComposite_invariant W p g⟩
  invFun f := scalarQuotientDesc W p f.val f.property
  left_inv g := (scalarQuotientDesc_unique W p _ _ g rfl).symm
  right_inv f := Subtype.ext (scalarQuotientDesc_fac W p f.val f.property)

end WeierstrassCurve.CubicCharts
