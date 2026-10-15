/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFiniteFiberGeometricSections
public import FLT.Mazur.AffineHilbertEnvelopeFiberCount

/-!
# Enumerating the original independent envelope on a common geometric test

Every original independent fiber has a finite family of actual maps on one
separably closed test. Their envelope points are distinct even when their
images in the translation scheme coincide. No splitting of original residue
fields, degree equality, or original relation witness is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.HilbertChart.AffineRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]
  (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  {A : Over (Spec (.of R))} {K : Type} [Field K] [IsSepClosed K]
  {t : Spec (.of K) ⟶ Spec (.of R)} (b : Over.mk t ⟶ A)
local notation "η" => (default : Spec (CommRingCat.of K))
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

/-- The original independent fiber is exhausted by constructed maps on the same test. -/
theorem exists_independent_geometric_sections :
    ∃ e : Fin (π ⁻¹' {b.left η}).ncard → (Over.mk t ⟶ prod A V),
      (∀ i, e i ≫ prod.fst = b) ∧ Function.Injective (fun i ↦ (e i).left η) ∧
      Set.range (fun i ↦ (e i).left η) = π ⁻¹' {b.left η} := by
  have hp : π = (Over.prodLeftIsoPullback A V).hom ≫ pullback.fst A.hom V.hom :=
    (Over.prodLeftIsoPullback_hom_fst A V).symm
  let _ : Etale π := by rw [hp]; infer_instance
  obtain ⟨a, ha, hi, hr⟩ := EtaleFiniteFiberGeometricSections.exists_enumeration π b.left
    (independentEnvelope_finite_fiber V (b.left η))
  have hw (i : Fin (π ⁻¹' {b.left η}).ncard) : a i ≫ (prod A V).hom = t := by
    rw [← (prod.fst : prod A V ⟶ A).w, ← Category.assoc, ha i, b.w]
    rfl
  let e (i : Fin (π ⁻¹' {b.left η}).ncard) : Over.mk t ⟶ prod A V :=
    Over.homMk (a i) (hw i)
  exact ⟨e, fun i ↦ Over.OverMorphism.ext (ha i), hi, hr⟩

omit [Etale V.hom] [IsAffine V.left] [IsSepClosed K] in
/-- Exact envelope coordinates distinguish original relation lifts on this geometric test. -/
theorem geometric_relation_lifts_injective {Z : Over (Spec (.of R))}
    (j : Z ⟶ prod A V) {n : ℕ} (e : Fin n → (Over.mk t ⟶ prod A V))
    (hi : Function.Injective (fun i ↦ (e i).left η))
    (z : Fin n → (Over.mk t ⟶ Z)) (hz : ∀ i, z i ≫ j = e i) :
    Function.Injective (fun i ↦ (z i).left η) := by
  intro i l hil
  apply hi
  have h (i : Fin n) := congrArg
    (fun a : Over.mk t ⟶ prod A V ↦ a.left η) (hz i)
  exact (h i).symm.trans ((congrArg j.left hil).trans (h l))

end FLT.Mazur.HilbertChart.AffineRestriction
