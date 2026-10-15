/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertGeometricAcyclicFiber
public import FLT.Mazur.VariableHilbertAcyclicLiftCriterion

/-!
# Necessity of the original geometric Hilbert conditions

Fullness lifts every independent geometric envelope map to the ORIGINAL
relation. Its first endpoint supplies the actual acyclic divisor class and
the retained constructed parameter. Thus the sufficient conditions are exact,
not additional assumptions hidden behind a purported global coverage result.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
  {K : Type} [Field K] {t : Spec (.of K) ⟶ Spec (.of R)} (b : Over.mk t ⟶ A)
local notation "η" => (default : Spec (CommRingCat.of K))
local notation "σ" => sectionAt f hL d V c k
local notation "s" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) σ
local notation "j" => toEnvelope f hL d V c k
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

omit [Etale V.hom] [IsAffine V.left] in
/-- Fullness at the original point lifts every whole geometric envelope map. -/
theorem exists_geometric_relation_lift_of_full
    (h : b.left η ∈ fullEnvelopeLocus f hL d V c k) (v : Over.mk t ⟶ V) :
    ∃ z : Over.mk t ⟶ relation f hL d V c k, z ≫ j = prod.lift b v := by
  let e : Over.mk t ⟶ prod A V := prod.lift b v
  have hr : Set.range e.left ⊆ Set.range (j).left := by
    rintro _ ⟨u, rfl⟩
    apply (mem_fullFiberLocus π (j).left.opensRange (b.left η)).mp h
    have he : e ≫ prod.fst = b := prod.lift_fst _ _
    have hp := congrArg (fun a : Over.mk t ⟶ A ↦ a.left u) he
    exact hp.trans (congrArg b.left (Subsingleton.elim (α := Spec (.of K)) u η))
  let z₀ := IsOpenImmersion.lift (j).left e.left hr
  have hz : z₀ ≫ (j).left = e.left := IsOpenImmersion.lift_fac _ _ hr
  have hw : z₀ ≫ (relation f hL d V c k).hom = t := by
    rw [← (j).w, ← Category.assoc, hz, e.w]
    rfl
  exact ⟨Over.homMk z₀ hw, Over.OverMorphism.ext hz⟩

omit [Etale V.hom] [IsAffine V.left] in
/-- Every translation on a full fiber yields its actual acyclic class and retained parameter. -/
theorem geometric_acyclic_retention_of_full
    (h : b.left η ∈ fullEnvelopeLocus f hL d V c k) (v : Over.mk t ⟶ V) :
    ∃ hs : s * (relativeFppfSheaf f).obj.map v.op c ∈
        (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)),
      (acyclicTranslationLift f hL d V c s v hs).left η ∈ Set.range k.left := by
  obtain ⟨z, hz⟩ := exists_geometric_relation_lift_of_full f hL d V c k b h v
  have hq : z ≫ snd f hL d V c k = b := by
    rw [← toEnvelope_test, ← Category.assoc, hz, prod.lift_fst]
  let a := z ≫ fst f hL d V c k
  have hv : (a ≫ k) ≫ variableHilbertBase f d V = v := by
    rw [Category.assoc]
    change (z ≫ fst f hL d V c k) ≫ k ≫ variableHilbertBase f d V = v
    rw [Category.assoc, ← toEnvelope_base, ← Category.assoc, hz, prod.lift_snd]
  have hc : (relativeFppfSheaf f).obj.map a.op σ = s := by
    have he := congrArg (fun u ↦ (relativeFppfSheaf f).obj.map z.op u)
      (equal_class f hL d V c k)
    simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hq] using he
  have hc' : (relativeFppfSheaf f).obj.map (a ≫ k).op
      (variableChartSection f hL d V c) = s := by
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    exact hc
  have hs := (acyclicTranslation_mem_iff_exists f hL d V c s v).mpr ⟨a ≫ k, hv, hc'⟩
  refine ⟨hs, ?_⟩
  have ha := acyclicTranslationLift_unique f hL d V c s v hs (a ≫ k) hv hc'
  rw [← ha]
  exact ⟨a.left η, rfl⟩

/-- The constructed geometric acyclic and retention conditions characterize fullness exactly. -/
theorem fullEnvelopeLocus_iff_geometric_acyclic_retention [IsSepClosed K] :
    b.left η ∈ fullEnvelopeLocus f hL d V c k ↔
    ∀ v : Over.mk t ⟶ V, ∃ hs : s * (relativeFppfSheaf f).obj.map v.op c ∈
        (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)),
      (acyclicTranslationLift f hL d V c s v hs).left η ∈ Set.range k.left := by
  constructor
  · exact geometric_acyclic_retention_of_full f hL d V c k b
  · intro h
    choose hA hr using h
    exact fullEnvelopeLocus_of_all_geometric_translations f hL d V c k b hA hr

end FLT.Mazur.HilbertChart.AffineRestriction
