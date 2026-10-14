/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteModelFlatPicard
public import FLT.Mazur.FlatDominantPrincipalNeighborhood

/-!
# Constructed nonreduced principal full Picard fppf neighborhoods

Generic point coverage in an unramified flat finite model produces an actual
nonnilpotent target coefficient. Its principal open has a whole-source fppf
projection, and every full kernel test has its unique original relation arrow.
The geometric and generic coverage hypotheses remain explicit.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "v" => finiteKernelProjection f hL d V c k
local notation "H" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "m" => pullback.lift p q H
local notation "K" => (pullback (Over.Hom.left v) (Over.Hom.left v) : Scheme)
local notation "b" => pullback.fst (Over.Hom.left v) (Over.Hom.left v) ≫ (Over.Hom.left v)
local notation "T" => (Over.left (finiteKernelModel f hL d V c k) : Scheme)
local notation "D" => (Over.left (relation f hL d V c k) : Scheme)
local instance finitePrincipalFppfKernelMono : Mono m :=
  modelRelationKernelMap_mono f hL d V c k (v).left H


variable [Flat (finiteKernelProjection f hL d V c k).left]
  [FormallyUnramified (finiteKernelProjection f hL d V c k).left]
  [IrreducibleSpace (finiteKernelModel f hL d V c k).left]

/-- Construct a principal whole-source fppf neighborhood with full original relation recovery.
This is a scheme-level inverse on arbitrary tests, including nonreduced tests. -/
theorem finiteModel_exists_principal_fppf_of_generic_image
    (hg : ∀ x : K, b x = genericPoint T → x ∈ Set.range m) :
    ∃ r : Γ(T, ⊤), ¬ IsNilpotent r ∧
      Flat (pullback.snd (v).left ((T).basicOpen r).ι) ∧
      Surjective (pullback.snd (v).left ((T).basicOpen r).ι) ∧
      ∀ (Z : Scheme) (a : Z ⟶ K), (Set.range (a ≫ b) ⊆ (T).basicOpen r) →
        ∃! z : Z ⟶ D, z ≫ m = a := by
  obtain ⟨x⟩ := (finiteModelEffectiveTarget_nonempty_iff_generic_image f hL d V c k).mpr hg
  have hn : (MonomorphismRelativeOpen.targetOpen m b : Set T).Nonempty :=
    ⟨x.val, x.property⟩
  obtain ⟨r, hr, he, hf, hs⟩ := SchemeFppfTargetOpen.exists_principal_fppf_of_nonempty
    (v).left (MonomorphismRelativeOpen.targetOpen m b) hn
  exact ⟨r, hr, hf, hs, fun Z a ha ↦
    MonomorphismRelativeOpen.test_lift m b a (ha.trans he)⟩

/-- The constructed principal target really receives an original source point.
Nonzero nilpotents cannot supply this witness. -/
theorem finiteModel_exists_source_principal_fppf_of_generic_image
    (hg : ∀ x : K, b x = genericPoint T → x ∈ Set.range m) :
    ∃ (r : Γ(T, ⊤)) (x : A.left), (v).left x ∈ (T).basicOpen r ∧
      ¬ IsNilpotent r ∧ Flat (pullback.snd (v).left ((T).basicOpen r).ι) ∧
      Surjective (pullback.snd (v).left ((T).basicOpen r).ι) ∧
      ∀ (Z : Scheme) (a : Z ⟶ K), (Set.range (a ≫ b) ⊆ (T).basicOpen r) →
        ∃! z : Z ⟶ D, z ≫ m = a := by
  obtain ⟨r, hr, hf, hs, hl⟩ :=
    finiteModel_exists_principal_fppf_of_generic_image f hL d V c k hg
  have hn : ((T).basicOpen r : Set T).Nonempty :=
    ((T).basicOpen r).ne_bot_iff_nonempty.mp
      (fun h ↦ hr ((Scheme.isNilpotent_iff_basicOpen_eq_bot r).mpr h))
  obtain ⟨y, hy⟩ := hn
  obtain ⟨z, hz⟩ := hs.1 ⟨y, hy⟩
  refine ⟨r, pullback.fst (v).left ((T).basicOpen r).ι z, ?_, hr, hf, hs, hl⟩
  have he := congrArg (fun g ↦ g z)
    (pullback.condition (f := (v).left) (g := ((T).basicOpen r).ι))
  change (v).left (pullback.fst (v).left ((T).basicOpen r).ι z) =
    ((T).basicOpen r).ι (pullback.snd (v).left ((T).basicOpen r).ι z) at he
  rw [he, hz]
  exact hy

end FLT.Mazur.HilbertChart.AffineRestriction
