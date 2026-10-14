/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteModelPrincipalInverses
public import FLT.Mazur.KernelPairUnramifiedInverse

/-!
# Constructing inverse charts from unramified finite Picard models

The etale endpoint of the actual original relation constructs all principal
inverse charts when the finite coefficient projection is unramified. Coverage
of the generic kernel by original relation points then constructs an actual
nonnilpotent coefficient certificate. Neither condition is asserted for every
selected translation; all original nonreduced structures are retained.
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
local instance finiteUnramifiedInverseKernelMono : Mono m :=
  modelRelationKernelMap_mono f hL d V c k (v).left H


variable [FormallyUnramified (finiteKernelProjection f hL d V c k).left]

/-- The actual proper-family relation comparison is etale over an unramified finite model. -/
theorem finiteModelRelationComparison_etale : Etale m :=
  KernelPairEffectiveOpen.comparison_etale_of_unramified p q (v).left H

/-- Every original relation image point has a scheme inverse, including its nilpotents. -/
theorem finiteModelInverseLocus_eq_range :
    (MonomorphismOpenImage.locus m : Set K) = Set.range m :=
  KernelPairEffectiveOpen.inverseLocus_eq_range_of_unramified p q (v).left H

/-- Construct finitely many principal inverses covering the entire original relation image. -/
theorem finiteModel_exists_principal_inverses_of_unramified :
    ∃ s : Finset Γ(K, ⊤),
      (∀ r ∈ s, ∃ a : ((K).basicOpen r).toScheme ⟶ D, a ≫ m = ((K).basicOpen r).ι) ∧
      ∀ x : K, x ∈ Set.range m ↔ ∃ r ∈ s, x ∈ (K).basicOpen r := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ : IsNoetherian K := ⟨⟩
  exact KernelPairEffectiveOpen.exists_principal_inverses_of_unramified p q (v).left H

variable [IrreducibleSpace (finiteKernelModel f hL d V c k).left]

/-- On possibly nonreduced irreducible models, generic point coverage constructs effectivity. -/
theorem finiteModelEffectiveTarget_nonempty_iff_generic_image :
    Nonempty (modelEffectiveTarget f hL d V c k v H).left ↔
      ∀ x : K, b x = genericPoint T → x ∈ Set.range m := by
  let _ : IsNoetherian A.left := by
    let _ := selectedHilbertSource_isLocallyNoetherian f d V k
    exact ⟨⟩
  have he : Nonempty (modelEffectiveTarget f hL d V c k v H).left ↔
      (KernelPairEffectiveOpen.targetOpen p q (v).left H : Set T).Nonempty :=
    ⟨fun ⟨x⟩ ↦ ⟨x.val, x.property⟩, fun ⟨x, hx⟩ ↦ ⟨⟨x, hx⟩⟩⟩
  rw [he]
  exact KernelPairEffectiveOpen.targetOpen_nonempty_iff_generic_image p q (v).left H

/-- Construct both principal original inverses and a nonnilpotent original target coefficient.
The assumptions concern unramified geometry and point coverage, not inverse morphisms. -/
theorem finiteModel_exists_coefficient_of_generic_image
    (hg : ∀ x : K, b x = genericPoint T → x ∈ Set.range m) :
    ∃ (s : Finset Γ(K, ⊤)) (r : Γ(T, ⊤)),
      (∀ t ∈ s, ∃ a : ((K).basicOpen t).toScheme ⟶ D, a ≫ m = ((K).basicOpen t).ι) ∧
      (b).appTop r ∈ Ideal.span (s : Set Γ(K, ⊤)) ∧ ¬ IsNilpotent r :=
  (finiteModelEffectiveTarget_nonempty_iff_coefficient f hL d V c k).mp
    ((finiteModelEffectiveTarget_nonempty_iff_generic_image f hL d V c k).mpr hg)

end FLT.Mazur.HilbertChart.AffineRestriction
