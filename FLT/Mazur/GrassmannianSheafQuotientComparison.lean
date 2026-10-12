/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSheafQuotientCommonTest
public import FLT.Mazur.GrassmannianSheafQuotientClassification
public import FLT.Mazur.ModuleSheafQuotientComparisonGluing

/-!
# Full quotient comparison across arbitrary source covers

Refine the actual intersections of the two original atlases. Equal classifying
maps identify their full relations, and the ambient epimorphism forces descent.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable {X : Scheme.{u}} (β : X ⟶ Spec (.of R))
  {P Q : X.Modules} (p : grassmannianSchemeAmbient (M := M) β ⟶ P) [Epi p]
  (q : grassmannianSchemeAmbient (M := M) β ⟶ Q)
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf

/-- A common classification constructs an isomorphism of the full original quotients. -/
theorem SheafQuotientClassifies.exists_iso
    {f : X ⟶ ambientGrassmannianScheme R M κ d}
    (h : SheafQuotientClassifies β p b hκ f)
    (h' : SheafQuotientClassifies β q b hκ f) :
    ∃ e : P ≅ Q, p ≫ e.hom = q := by
  unfold SheafQuotientClassifies at h h'
  obtain ⟨C, aC, hC, N, hf, he⟩ := h
  obtain ⟨D, aD, hD, N', hf', he'⟩ := h'
  let _ := aC
  let _ := aD
  let U : X.OpenCover := C.openCover.bind fun j ↦ D.openCover.pullback₁ (C.f j)
  obtain ⟨E, v, w, l, r, hl, hr⟩ :
      ∃ (E : X.AffineOpenCover.{u}) (v : E.I₀ → C.I₀) (w : E.I₀ → D.I₀)
        (l : ∀ j, Spec (E.X j) ⟶ Spec (C.X (v j)))
        (r : ∀ j, Spec (E.X j) ⟶ Spec (D.X (w j))),
        (∀ j, l j ≫ C.f (v j) = E.f j) ∧ (∀ j, r j ≫ D.f (w j) = E.f j) := by
    refine ⟨U.affineRefinement, (fun j ↦ j.1.1), (fun j ↦ j.1.2),
      (fun j ↦ (U.X j.1).affineCover.f j.2 ≫ Limits.pullback.fst _ _),
      (fun j ↦ (U.X j.1).affineCover.f j.2 ≫ Limits.pullback.snd _ _), ?_, ?_⟩
    · intro j
      rfl
    · intro j
      exact (Category.assoc _ _ _).trans
        ((congrArg ((U.X j.1).affineCover.f j.2 ≫ ·)
          (Limits.pullback.condition (f := C.f j.1.1) (g := D.f j.1.2)).symm).trans
            (Category.assoc _ _ _).symm)
  let aE : ∀ j, Algebra R (E.X j) := fun j ↦
    (Spec.preimage (E.f j ≫ β)).hom.toAlgebra
  let _ := aE
  have hE : ∀ j, E.f j ≫ β = Spec.algebraMap R (E.X j) :=
    fun j ↦ (Spec.map_preimage _).symm
  let s (j : E.I₀) : C.X (v j) →ₐ[R] E.X j :=
    affineOverAlgHom R (C.X (v j)) (E.X j) (l j) (by
      change l j ≫ Spec.algebraMap R (C.X (v j)) = Spec.algebraMap R (E.X j)
      rw [← hC (v j), ← Category.assoc, hl j, hE j])
  let t (j : E.I₀) : D.X (w j) →ₐ[R] E.X j :=
    affineOverAlgHom R (D.X (w j)) (E.X j) (r j) (by
      change r j ≫ Spec.algebraMap R (D.X (w j)) = Spec.algebraMap R (E.X j)
      rw [← hD (w j), ← Category.assoc, hr j, hE j])
  have hs (j : E.I₀) : Spec.map (CommRingCat.ofHom (s j).toRingHom) ≫ C.f (v j) =
      E.f j := by rw [affineOverAlgHom_spec]; exact hl j
  have ht (j : E.I₀) : Spec.map (CommRingCat.ofHom (t j).toRingHom) ≫ D.f (w j) =
      E.f j := by rw [affineOverAlgHom_spec]; exact hr j
  have hc (j : E.I₀) : ∃ e : (pullback (E.f j)).obj P ≅ (pullback (E.f j)).obj Q,
      (pullback (E.f j)).map p ≫ e.hom = (pullback (E.f j)).map q :=
    exists_sheafQuotientCommonTestIso (T := E.X j) b hκ β p q
      (C.f (v j)) (hC (v j)) (D.f (w j)) (hD (w j)) (E.f j) (hE j)
      (s j) (hs j) (t j) (ht j) (N (v j)) (N' (w j))
      (he (v j)).choose (he' (w j)).choose (he (v j)).choose_spec (he' (w j)).choose_spec
      f (hf (v j)) (hf' (w j))
  let e := fun j ↦ (hc j).choose
  have hep := fun j ↦ (hc j).choose_spec
  have hcov : ∀ x : X, ∃ j, x ∈ Set.range (E.f j) :=
    fun x ↦ ⟨E.idx x, E.covers x⟩
  let a := fun j ↦ (e j).hom
  have hiso : ∀ j, IsIso (a j) := fun _ ↦ inferInstance
  exact ⟨ModuleSheafQuotientComparisonGluing.quotientComparisonIso
      (fun j ↦ Spec (E.X j)) E.f p q a hep hcov hiso,
    ModuleSheafQuotientComparisonGluing.quotientComparisonIso_projection
      (fun j ↦ Spec (E.X j)) E.f p q a hep hcov hiso⟩

end FLT.Mazur.GrassmannianChart
