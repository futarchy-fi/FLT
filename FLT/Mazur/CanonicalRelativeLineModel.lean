/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineRelativeLineModel
public import FLT.Mazur.RelativePicardFppfCover
public import FLT.Mazur.RelativePicardFppfSheaf

/-!
# Finitely presented line models in the original Picard convention

The relative line model can be chosen on the canonical fiber product over
its parameter base. The actual line is recovered by the original total-space
map, so its original relative fppf class is the restriction of the model class.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.Approximation
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f]

/-- An affine-test line descends on the canonical Picard total spaces, with full recovery. -/
theorem exists_canonical_relative_line_model (T : Over (Spec (.of R))) [IsAffine T.left]
    (L : LineBundle (pullback f T.hom)) :
    ∃ (V : Over (Spec (.of R))) (b : T ⟶ V)
      (M : LineBundle (pullback f V.hom)),
      IsAffine V.left ∧ IsLocallyNoetherian V.left ∧ LocallyOfFinitePresentation V.hom ∧
        Nonempty ((Scheme.Modules.pullback (relativeTotalMap f b)).obj M.val ≅ L.val) := by
  obtain ⟨Z, B, r, t, p, b, u, M, hB, hN, hu, HB, Hp, ht, hb, hM, ⟨e⟩⟩ :=
    exists_affine_relative_line_model (IsPullback.of_hasPullback f T.hom) L.val L.property
  let V := Over.mk u
  let a : T ⟶ V := Over.homMk b hb
  let N := (Scheme.Modules.pullback HB.isoPullback.inv).obj M
  have hN' := hM.pullback HB.isoPullback.inv
  have hp : p ≫ HB.isoPullback.hom = relativeTotalMap f a := by
    apply pullback.hom_ext
    · rw [Category.assoc, HB.isoPullback_hom_fst, ht]
      exact (relativeTotalMap_fst f a).symm
    · rw [Category.assoc, HB.isoPullback_hom_snd]
      exact Hp.w.trans (relativeTotalMap_snd f a).symm
  have hp' : relativeTotalMap f a ≫ HB.isoPullback.inv = p := by
    rw [← hp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨V, a, ⟨N, hN'⟩, hB, hN, hu, ⟨?_⟩⟩
  exact ((Scheme.Modules.pullbackComp (relativeTotalMap f a) HB.isoPullback.inv).app M)
    ≪≫ (eqToIso (congrArg (fun k ↦ (Scheme.Modules.pullback k).obj M) hp')) ≪≫ e

omit [Algebra.FiniteType ℤ R] [IsProper f] in
/-- Recovery of the full line implies recovery of its original sheaf class. -/
theorem canonical_relative_line_model_class {T V : Over (Spec (.of R))} (b : T ⟶ V)
    (L : LineBundle (pullback f T.hom)) (M : LineBundle (pullback f V.hom))
    (e : (Scheme.Modules.pullback (relativeTotalMap f b)).obj M.val ≅ L.val) :
    (relativeFppfSheaf f).obj.map b.op
        (relativeFppfClass f V (relativeClass _ (mk M.val M.property))) =
      relativeFppfClass f T (relativeClass _ (mk L.val L.property)) := by
  rw [relativeFppfClass_naturality, relativeBaseMap_class, pullback_mk,
    mk_eq_of_iso _ _ e]

end FLT.Mazur.Approximation
