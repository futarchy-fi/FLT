/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertGeometricFiberNecessity

/-!
# Exact acyclicity and retention for one original envelope map

The criterion applies to whole scheme tests, including nilpotents, without
assuming that every point in the ambient fiber already belongs to the relation.
On a field test it detects the individual independent envelope point. This
allows residual generic witnesses to be tested one coordinate at a time.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "σ" => sectionAt f hL d V c k
local notation "j" => toEnvelope f hL d V c k

/-- An individual whole scheme envelope map lifts exactly when its constructed parameter is kept. -/
theorem original_envelope_lift_iff {T : Over (Spec (.of R))} (b : T ⟶ A) (v : T ⟶ V) :
    (∃ z : T ⟶ relation f hL d V c k, z ≫ j = prod.lift b v) ↔
      ∃ hs : (relativeFppfSheaf f).obj.map b.op σ *
          (relativeFppfSheaf f).obj.map v.op c ∈
          (acyclicDegreePicardSubfunctor f d).obj (op T),
        Set.range (acyclicTranslationLift f hL d V c
          ((relativeFppfSheaf f).obj.map b.op σ) v hs).left ⊆ Set.range k.left := by
  constructor
  · rintro ⟨z, hz⟩
    let a := z ≫ fst f hL d V c k
    have hq : z ≫ snd f hL d V c k = b := by
      rw [← toEnvelope_test, ← Category.assoc, hz, prod.lift_fst]
    have hv : (a ≫ k) ≫ variableHilbertBase f d V = v := by
      change (z ≫ fst f hL d V c k) ≫ k ≫ variableHilbertBase f d V = v
      rw [Category.assoc, ← toEnvelope_base, ← Category.assoc, hz, prod.lift_snd]
    have hc₀ : (relativeFppfSheaf f).obj.map a.op σ =
        (relativeFppfSheaf f).obj.map b.op σ := by
      have he := congrArg (fun u ↦ (relativeFppfSheaf f).obj.map z.op u)
        (equal_class f hL d V c k)
      simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hq] using he
    have hc : (relativeFppfSheaf f).obj.map (a ≫ k).op
        (variableChartSection f hL d V c) = (relativeFppfSheaf f).obj.map b.op σ := by
      rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      exact hc₀
    have hs := (acyclicTranslation_mem_iff_exists f hL d V c _ v).mpr ⟨a ≫ k, hv, hc⟩
    refine ⟨hs, ?_⟩
    rw [← acyclicTranslationLift_unique f hL d V c _ v hs (a ≫ k) hv hc]
    rintro _ ⟨u, rfl⟩
    exact ⟨a.left u, rfl⟩
  · rintro ⟨hs, hr⟩
    exact exists_acyclic_relation_lift f hL d V c k b v hs hr

/-- One field-valued coordinate is present exactly when acyclicity and retention hold. -/
theorem original_envelope_geometric_mem_iff {K : Type} [Field K]
    {t : Spec (.of K) ⟶ Spec (.of R)} (b : Over.mk t ⟶ A) (v : Over.mk t ⟶ V) :
    (prod.lift b v).left (default : Spec (.of K)) ∈ (j).left.opensRange ↔
      ∃ hs : (relativeFppfSheaf f).obj.map b.op σ *
          (relativeFppfSheaf f).obj.map v.op c ∈
          (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)),
        (acyclicTranslationLift f hL d V c
          ((relativeFppfSheaf f).obj.map b.op σ) v hs).left
            (default : Spec (.of K)) ∈ Set.range k.left := by
  constructor
  · intro h
    let e : Over.mk t ⟶ prod A V := prod.lift b v
    have hr : Set.range e.left ⊆ Set.range (j).left := by
      rintro _ ⟨u, rfl⟩
      rw [Subsingleton.elim (α := Spec (.of K)) u (default : Spec (.of K))]
      exact h
    let z₀ := IsOpenImmersion.lift (j).left e.left hr
    have hz : z₀ ≫ (j).left = e.left := IsOpenImmersion.lift_fac _ _ _
    let z : Over.mk t ⟶ relation f hL d V c k := Over.homMk z₀ (by
      rw [← (j).w, ← Category.assoc, hz, e.w])
    obtain ⟨hs, hret⟩ := (original_envelope_lift_iff f hL d V c k b v).mp
      ⟨z, Over.OverMorphism.ext hz⟩
    exact ⟨hs, hret ⟨(default : Spec (.of K)), rfl⟩⟩
  · rintro ⟨hs, hret⟩
    obtain ⟨z, hz⟩ := exists_acyclic_geometric_relation_lift f hL d V c k b v rfl
      hs (default : Spec (.of K)) hret
    exact ⟨z.left (default : Spec (.of K)), congrArg (fun a : Over.mk t ⟶ prod A V ↦
      a.left (default : Spec (.of K))) hz⟩

end FLT.Mazur.HilbertChart.AffineRestriction
