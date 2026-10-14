/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteModelPrincipalInverses
public import FLT.Mazur.KernelPairGenericEtaleCertificates

/-!
# Original Picard coefficients from etale neighborhoods of the entire generic kernel

The tests take place on the unrestricted nonreduced finite model. Each actual
etale neighborhood carries a full original Picard relation arrow, with both
endpoints retained. Descent constructs the inverse charts and a nonnilpotent
coefficient; no unramifiedness premise is imposed on the original projection.
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
local instance finiteEtaleCertificateKernelMono : Mono m :=
  modelRelationKernelMap_mono f hL d V c k (v).left H

variable [IrreducibleSpace (finiteKernelModel f hL d V c k).left]

/-- Actual original arrows on etale neighborhoods of every generic kernel point suffice. -/
theorem finiteModelEffectiveTarget_nonempty_of_generic_etale_lifts
    (hg : ∀ x : K, b x = genericPoint T →
      ∃ (Z : Scheme) (t : Z ⟶ K) (a : Z ⟶ D) (z : Z), Etale t ∧
        a ≫ p = t ≫ pullback.fst (v).left (v).left ∧
        a ≫ q = t ≫ pullback.snd (v).left (v).left ∧ t z = x) :
    Nonempty (modelEffectiveTarget f hL d V c k v H).left := by
  let _ : IsNoetherian A.left := by
    let _ := selectedHilbertSource_isLocallyNoetherian f d V k
    exact ⟨⟩
  have hn := KernelPairEffectiveOpen.targetOpen_nonempty_of_generic_etale_lifts p q (v).left H
    (fun x hx ↦ by
      obtain ⟨Z, t, a, z, ht, hp, hq, hz⟩ := hg x hx
      refine ⟨Z, t, a, z, ht, ?_, hz⟩
      apply pullback.hom_ext
      · simpa only [Category.assoc, pullback.lift_fst] using hp
      · simpa only [Category.assoc, pullback.lift_snd] using hq)
  exact ⟨⟨hn.choose, hn.choose_spec⟩⟩

/-- Generic etale arrows construct literal principal inverse and coefficient-ideal witnesses. -/
theorem finiteModel_exists_coefficient_of_generic_etale_lifts
    (hg : ∀ x : K, b x = genericPoint T →
      ∃ (Z : Scheme) (t : Z ⟶ K) (a : Z ⟶ D) (z : Z), Etale t ∧
        a ≫ p = t ≫ pullback.fst (v).left (v).left ∧
        a ≫ q = t ≫ pullback.snd (v).left (v).left ∧ t z = x) :
    ∃ (s : Finset Γ(K, ⊤)) (r : Γ(T, ⊤)),
      (∀ t ∈ s, ∃ a : ((K).basicOpen t).toScheme ⟶ D, a ≫ m = ((K).basicOpen t).ι) ∧
      (b).appTop r ∈ Ideal.span (s : Set Γ(K, ⊤)) ∧ ¬ IsNilpotent r :=
  (finiteModelEffectiveTarget_nonempty_iff_coefficient f hL d V c k).mp
    (finiteModelEffectiveTarget_nonempty_of_generic_etale_lifts f hL d V c k hg)

end FLT.Mazur.HilbertChart.AffineRestriction
