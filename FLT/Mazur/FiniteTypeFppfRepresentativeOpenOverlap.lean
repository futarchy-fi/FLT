/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeRelativeClassOpenNaturality

/-!
# Compatibility of the opens of independent local representatives

Two representatives of restrictions of one actual Picard-sheaf section
have equal pulled-back opens on every common test. This supplies the
actual scheme fiber-product overlap equality required for open descent.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]

/-- Independent local representatives yield identical opens on every common test. -/
theorem finiteTypeFppfRepresentativeOpen_overlap
    {T U V W : Over (Spec (.of R))} (a : U ⟶ T) (b : V ⟶ T)
    (p : W ⟶ U) (q : W ⟶ V) (hpq : p ≫ a = q ≫ b)
    (s : (relativeFppfSheaf f).obj.obj (op T))
    (c : RelativePic (Limits.pullback.snd f U.hom))
    (d : RelativePic (Limits.pullback.snd f V.hom))
    (hc : relativeFppfClass f U c = (relativeFppfSheaf f).obj.map a.op s)
    (hd : relativeFppfClass f V d = (relativeFppfSheaf f).obj.map b.op s) :
    p.left ⁻¹ᵁ finiteTypeRelativeClassOpen f U c =
      q.left ⁻¹ᵁ finiteTypeRelativeClassOpen f V d := by
  rw [← finiteTypeRelativeClassOpen_map, ← finiteTypeRelativeClassOpen_map]
  apply finiteTypeRelativeClassOpen_fppf_eq
  rw [← relativeFppfClass_naturality, ← relativeFppfClass_naturality, hc, hd]
  have h := congrArg (fun k : W ⟶ T ↦ (relativeFppfSheaf f).obj.map k.op s) hpq
  simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using h

/-- The actual scheme pullback of two local test arrows has compatible representative opens. -/
theorem finiteTypeFppfRepresentativeOpen_pullback
    {T U V : Over (Spec (.of R))} (a : U ⟶ T) (b : V ⟶ T)
    (s : (relativeFppfSheaf f).obj.obj (op T))
    (c : RelativePic (Limits.pullback.snd f U.hom))
    (d : RelativePic (Limits.pullback.snd f V.hom))
    (hc : relativeFppfClass f U c = (relativeFppfSheaf f).obj.map a.op s)
    (hd : relativeFppfClass f V d = (relativeFppfSheaf f).obj.map b.op s) :
    (Limits.pullback.fst a.left b.left) ⁻¹ᵁ finiteTypeRelativeClassOpen f U c =
      (Limits.pullback.snd a.left b.left) ⁻¹ᵁ finiteTypeRelativeClassOpen f V d := by
  let W := Over.mk (Limits.pullback.fst a.left b.left ≫ U.hom)
  let p : W ⟶ U := Over.homMk (Limits.pullback.fst a.left b.left)
  let q : W ⟶ V := Over.homMk (Limits.pullback.snd a.left b.left) (by
    dsimp [W]
    rw [← Over.w a, ← Over.w b, ← Category.assoc, ← Category.assoc,
      Limits.pullback.condition])
  exact finiteTypeFppfRepresentativeOpen_overlap f a b p q
    (Over.OverMorphism.ext (Limits.pullback.condition)) s c d hc hd

end FLT.Mazur.CartierAbel
