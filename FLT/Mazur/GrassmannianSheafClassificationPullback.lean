/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianCanonicalSheafClassification
public import FLT.Mazur.GrassmannianSheafQuotientPullback
public import FLT.Mazur.ModuleSheafLocalFrames

/-!
# Arbitrary-source naturality of original sheaf quotient classification

Refine the actual pullback of the source cover. The refined original coefficient
maps retain every relation and every ambient projection.
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
variable {X Y : Scheme.{u}} (β : X ⟶ Spec (.of R))
  {P : X.Modules} (p : grassmannianSchemeAmbient (M := M) β ⟶ P)
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf

/-- Original quotient classification is preserved by arbitrary scheme pullback. -/
theorem SheafQuotientClassifies.pullback
    {f : X ⟶ ambientGrassmannianScheme R M κ d}
    (h : SheafQuotientClassifies β p b hκ f) (g : Y ⟶ X) :
    SheafQuotientClassifies (g ≫ β) (sheafQuotientPullbackMap β g p) b hκ (g ≫ f) := by
  unfold SheafQuotientClassifies at h ⊢
  obtain ⟨C, a, hC, N, hf, he⟩ := h
  let _ := a
  let U : Y.OpenCover := C.openCover.pullback₁ g
  obtain ⟨D, v, t, ht⟩ : ∃ (D : Y.AffineOpenCover.{u}) (v : D.I₀ → C.I₀)
      (t : ∀ j, Spec (D.X j) ⟶ Limits.pullback g (C.f (v j))),
      ∀ j, t j ≫ Limits.pullback.fst g (C.f (v j)) = D.f j :=
    ⟨U.affineRefinement, (fun j ↦ j.1), (fun j ↦ (U.X j.1).affineCover.f j.2),
      (fun _ ↦ rfl)⟩
  let aD : ∀ j, Algebra R (D.X j) := fun j ↦
    (Spec.preimage (D.f j ≫ g ≫ β)).hom.toAlgebra
  let _ := aD
  let hD : ∀ j, D.f j ≫ (g ≫ β) = Spec.algebraMap R (D.X j) :=
    fun j ↦ (Spec.map_preimage _).symm
  let l (j : D.I₀) : Spec (D.X j) ⟶ Spec (C.X (v j)) :=
    t j ≫ Limits.pullback.snd g (C.f (v j))
  have hl (j : D.I₀) : l j ≫ C.f (v j) = D.f j ≫ g := by
    dsimp only [l]
    rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc, ht j]
  let s (j : D.I₀) : C.X (v j) →ₐ[R] D.X j :=
    affineOverAlgHom R (C.X (v j)) (D.X j) (l j) (by
      change l j ≫ Spec.algebraMap R (C.X (v j)) = Spec.algebraMap R (D.X j)
      rw [← hC (v j), ← Category.assoc, hl j, Category.assoc, hD j])
  have hs (j : D.I₀) : Spec.map (CommRingCat.ofHom (s j).toRingHom) ≫ C.f (v j) =
      D.f j ≫ g := by rw [affineOverAlgHom_spec]; exact hl j
  refine ⟨D, aD, hD, (fun j ↦ Module.Grassmannian.map (s j) (N (v j))), ?_, ?_⟩
  · intro j
    rw [ambientClassifyingMap_natural (B := D.X j), ← hf (v j),
      ← Category.assoc (Spec.map (CommRingCat.ofHom (s j).toRingHom)), hs j,
      Category.assoc]
  · intro j
    exact ⟨sheafQuotientPullbackTestIso (B := D.X j) g (C.f (v j)) (D.f j) (s j) (hs j) (N (v j))
      (he (v j)).choose,
      sheafQuotientPullbackTestIso_projection (B := D.X j) β g p (C.f (v j)) (hC (v j)) (D.f j)
        (hD j) (s j) (hs j) (N (v j)) (he (v j)).choose (he (v j)).choose_spec⟩

/-- The constructed map commutes with arbitrary pullback of the whole original quotient. -/
theorem locallyFreeQuotientClassifyingMap_pullback [Epi p] {τ : Type u} [Fintype τ]
    (hP : ModuleSheafLocalFrames.HasFrames τ P) (hd : Fintype.card τ = d) (g : Y ⟶ X) :
    locallyFreeQuotientClassifyingMap (g ≫ β) (sheafQuotientPullbackMap β g p) b hκ
      (hP.pullback τ P g) hd = g ≫ locallyFreeQuotientClassifyingMap β p b hκ hP hd :=
  (locallyFreeQuotientClassifyingMap_spec _ _ b hκ (hP.pullback τ P g) hd).unique _ _ b hκ
    ((locallyFreeQuotientClassifyingMap_spec β p b hκ hP hd).pullback β p b hκ g)

end FLT.Mazur.GrassmannianChart
