/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CanonicalNonspecialDivisorCover
public import FLT.Mazur.RelativeFppfComparisonCover
public import FLT.Mazur.FiniteTypeAcyclicDivisorMap

/-!
# Full nonspecial divisors and original line representatives on one cover

Refine the smooth divisor cover by a cover representing the given Picard
section. The composed small fppf cover retains the original section and the
full divisor, on the canonical total space of every covering member.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)

include hB in
/-- Arbitrary original sheaf sections have lines and full nonspecial divisors on one cover. -/
theorem exists_nonspecial_divisor_line_cover (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T)) :
    ∃ C : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left, ∀ i,
      ∃ (_D : AcyclicRankOneRelativeDivisor (pullback.snd f (relativeCoverMember T C i).hom))
        (L : LineBundle (pullback f (relativeCoverMember T C i).hom)),
        relativeFppfClass f _ (relativeClass _ (mk L.val L.property)) =
          (relativeFppfSheaf f).obj.map (relativeCoverArrow T C i).op s := by
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨C, _, hD⟩ := exists_canonical_nonspecial_divisor_test_cover f B hB T
  have hrep (i : C.I₀) := relativeFppfClass_exists_cover f (relativeCoverMember T C i)
    ((relativeFppfSheaf f).obj.map (relativeCoverArrow T C i).op s)
  choose E hE using hrep
  let F := C.bind E
  refine ⟨F, fun i ↦ ?_⟩
  let a : relativeCoverMember T F i ⟶ relativeCoverMember T C i.1 :=
    Over.homMk ((E i.1).f i.2) (by simp only [relativeCoverMember]; rfl)
  let V := relativeCoverMember (relativeCoverMember T C i.1) (E i.1) i.2
  let b : relativeCoverMember T F i ⟶ V := Over.homMk (𝟙 _) (by
    simp only [relativeCoverMember, Category.id_comp]; rfl)
  obtain ⟨c, hc⟩ := hE i.1 i.2
  obtain ⟨L, hL⟩ := relativePic_exists_line (pullback.snd f V.hom) c
  let M := (Scheme.Modules.pullback (relativeTotalMap f b)).obj L.val
  have hM := L.property.pullback (relativeTotalMap f b)
  refine ⟨finiteTypeAcyclicDivisorMap f a (hD i.1).some, ⟨M, hM⟩, ?_⟩
  change relativeFppfClass f _ (relativeBaseMap f b (relativeClass _ (mk L.val L.property))) = _
  rw [hL, ← relativeFppfClass_naturality, hc]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  congr 2

end FLT.Mazur.CartierAbel
