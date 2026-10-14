/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteModelGenericEffectivity
public import FLT.Mazur.MonomorphismCoefficientEffectiveOpen

/-!
# Actual principal coefficient charts for full Picard relation inverses

Without reducing the coefficient model, construct a finite principal cover of
its entire known inverse locus. For an integral original parameter chart,
the represented full Picard region is nonempty exactly when finitely many
such principal inverse charts cover the complete generic candidate kernel.
The coverage condition itself is not proved for arbitrary translations.
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
local instance finitePrincipalInverseKernelMono : Mono m :=
  modelRelationKernelMap_mono f hL d V c k (v).left H

/-- Finitely many actual kernel coefficients cover the full inverse locus, with original arrows.
This construction also applies to nonreduced selected sources and coefficient models. -/
theorem finiteModel_exists_principal_inverse_cover :
    ∃ s : Finset Γ(K, ⊤), (⨆ r : s, (K).basicOpen r.val) = MonomorphismOpenImage.locus m ∧
      ∀ r ∈ s, ∃ a : ((K).basicOpen r).toScheme ⟶ D, a ≫ m = ((K).basicOpen r).ι := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ : IsNoetherian K := ⟨⟩
  exact MonomorphismOpenImage.exists_principal_inverse_cover m

/-- A nonempty full effective region is equivalent to a literal coefficient-ideal certificate.
This equivalence applies before any reduction or integrality assumption. -/
theorem finiteModelEffectiveTarget_nonempty_iff_coefficient :
    Nonempty (modelEffectiveTarget f hL d V c k v H).left ↔
      ∃ (s : Finset Γ(K, ⊤)) (r : Γ(T, ⊤)),
        (∀ t ∈ s, ∃ a : ((K).basicOpen t).toScheme ⟶ D, a ≫ m = ((K).basicOpen t).ι) ∧
        (b).appTop r ∈ Ideal.span (s : Set Γ(K, ⊤)) ∧ ¬ IsNilpotent r := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ : IsNoetherian K := ⟨⟩
  have he : Nonempty (modelEffectiveTarget f hL d V c k v H).left ↔
      (MonomorphismRelativeOpen.targetOpen m b : Set T).Nonempty :=
    ⟨fun ⟨x⟩ ↦ ⟨x.val, x.property⟩, fun ⟨x, hx⟩ ↦ ⟨⟨x, hx⟩⟩⟩
  rw [he]
  exact MonomorphismRelativeOpen.targetOpen_nonempty_iff_coefficient m b

variable [IsIntegral A.left]

/-- Nonemptiness of the represented original Picard region reduces to finitely many actual
coefficient localizations with scheme inverses covering the entire generic kernel fiber. -/
theorem finiteModelPicardFppfTarget_nonempty_iff_principal_inverses :
    Nonempty (finiteModelPicardFppfTarget f hL d V c k).left ↔
      ∃ s : Finset Γ(K, ⊤),
        (∀ r ∈ s, ∃ a : ((K).basicOpen r).toScheme ⟶ D, a ≫ m = ((K).basicOpen r).ι) ∧
        ∀ x : K, b x = genericPoint T → ∃ r ∈ s, x ∈ (K).basicOpen r := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ : IsNoetherian K := ⟨⟩
  rw [finiteModelPicardFppfTarget_nonempty_iff_genericFiber]
  exact MonomorphismOpenImage.subset_locus_iff_finite_principal m
    {x : K | b x = genericPoint T}

/-- Over integral original sources the same coefficient certificate gives represented fppf
nonemptiness of the full original Picard sheaf, without assuming the model is flat. -/
theorem finiteModelPicardFppfTarget_nonempty_iff_coefficient :
    Nonempty (finiteModelPicardFppfTarget f hL d V c k).left ↔
      ∃ (s : Finset Γ(K, ⊤)) (r : Γ(T, ⊤)),
        (∀ t ∈ s, ∃ a : ((K).basicOpen t).toScheme ⟶ D, a ≫ m = ((K).basicOpen t).ι) ∧
        (b).appTop r ∈ Ideal.span (s : Set Γ(K, ⊤)) ∧ ¬ IsNilpotent r := by
  rw [finiteModelPicardFppfTarget_nonempty_iff]
  exact finiteModelEffectiveTarget_nonempty_iff_coefficient f hL d V c k

end FLT.Mazur.HilbertChart.AffineRestriction
