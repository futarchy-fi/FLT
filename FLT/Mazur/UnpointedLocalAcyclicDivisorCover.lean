/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UnpointedAcyclicFppfImageEquivalence
public import FLT.Mazur.UnpointedLocalAcyclicFppfSheaf

/-!
# Matching full divisors for locally acyclic Picard-sheaf sections

Every section of the local acyclic subsheaf supplies actual full divisors
on an fppf cover. Their entire ideals agree on every common test, not just
their classes or supports. Global effective gluing remains separate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]

/-- Independently supplied full divisors of one sheaf section agree on every common test. -/
theorem finiteTypeAcyclicDivisor_overlap (T U V W : Over (Spec (.of R)))
    (a : U ⟶ T) (b : V ⟶ T) (p : W ⟶ U) (q : W ⟶ V) (hpq : p ≫ a = q ≫ b)
    (s : (relativeFppfSheaf f).obj.obj (op T))
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f U.hom))
    (E : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f V.hom))
    (hD : relativeFppfClass f U (abel (Limits.pullback.snd f U.hom) D.val) =
      (relativeFppfSheaf f).obj.map a.op s)
    (hE : relativeFppfClass f V (abel (Limits.pullback.snd f V.hom) E.val) =
      (relativeFppfSheaf f).obj.map b.op s) :
    finiteTypeAcyclicDivisorMap f p D = finiteTypeAcyclicDivisorMap f q E := by
  apply finiteTypeAcyclicAbelFppf_injective f W
  have hD' : relativeFppfClass f W
      (abel _ (finiteTypeAcyclicDivisorMap f p D).val) =
      (relativeFppfSheaf f).obj.map p.op ((relativeFppfSheaf f).obj.map a.op s) :=
    (congrArg (relativeFppfClass f W) (finiteTypeAcyclicDivisorMap_class f p D)).trans
      ((relativeFppfClass_naturality f p _).symm.trans
        (congrArg ((relativeFppfSheaf f).obj.map p.op) hD))
  have hE' : relativeFppfClass f W
      (abel _ (finiteTypeAcyclicDivisorMap f q E).val) =
      (relativeFppfSheaf f).obj.map q.op ((relativeFppfSheaf f).obj.map b.op s) :=
    (congrArg (relativeFppfClass f W) (finiteTypeAcyclicDivisorMap_class f q E)).trans
      ((relativeFppfClass_naturality f q _).symm.trans
        (congrArg ((relativeFppfSheaf f).obj.map q.op) hE))
  have he := ConcreteCategory.congr_hom
    (congrArg (fun g ↦ (relativeFppfSheaf f).obj.map g.op) hpq) s
  have he' : (relativeFppfSheaf f).obj.map p.op
      ((relativeFppfSheaf f).obj.map a.op s) =
      (relativeFppfSheaf f).obj.map q.op ((relativeFppfSheaf f).obj.map b.op s) := by
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using he
  exact hD'.trans (he'.trans hE'.symm)

/-- The overlap assertion retains the original full ideal comaps, including multiplicities. -/
theorem finiteTypeAcyclicDivisor_overlap_ideal (T U V W : Over (Spec (.of R)))
    (a : U ⟶ T) (b : V ⟶ T) (p : W ⟶ U) (q : W ⟶ V) (hpq : p ≫ a = q ≫ b)
    (s : (relativeFppfSheaf f).obj.obj (op T))
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f U.hom))
    (E : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f V.hom))
    (hD : relativeFppfClass f U (abel (Limits.pullback.snd f U.hom) D.val) =
      (relativeFppfSheaf f).obj.map a.op s)
    (hE : relativeFppfClass f V (abel (Limits.pullback.snd f V.hom) E.val) =
      (relativeFppfSheaf f).obj.map b.op s) :
    D.val.val.comap (relativeTotalMap f p) = E.val.val.comap (relativeTotalMap f q) := by
  simpa only [finiteTypeAcyclicDivisorMap_ideal] using congrArg (fun F ↦ F.val.val)
    (finiteTypeAcyclicDivisor_overlap f T U V W a b p q hpq s D E hD hE)

/-- Local acyclic membership produces a cover by actual full divisors with exact matching. -/
theorem localGeometricAcyclicFppf_exists_divisor_cover (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T))
    (hs : s ∈ (localGeometricAcyclicFppfSubfunctor f).obj (op T)) :
    ∃ (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
      (D : ∀ i, AcyclicRankOneRelativeDivisor
        (Limits.pullback.snd f (relativeCoverMember T 𝒰 i).hom)),
      (∀ i, relativeFppfClass f _ (abel _ (D i).val) =
        (relativeFppfSheaf f).obj.map (relativeCoverArrow T 𝒰 i).op s) ∧
      ∀ i j (V : Over (Spec (.of R)))
        (p : V ⟶ relativeCoverMember T 𝒰 i) (q : V ⟶ relativeCoverMember T 𝒰 j),
        p ≫ relativeCoverArrow T 𝒰 i = q ≫ relativeCoverArrow T 𝒰 j →
        (D i).val.val.comap (relativeTotalMap f p) =
          (D j).val.val.comap (relativeTotalMap f q) := by
  obtain ⟨𝒰, h𝒰⟩ := localGeometricAcyclicFppf_exists_cover f T s hs
  have hex (i : 𝒰.I₀) := finiteTypeUnpointedAcyclicFppf_existsUnique f
    (relativeCoverMember T 𝒰 i) _ (h𝒰 i)
  choose D hD using fun i ↦ (hex i).exists
  refine ⟨𝒰, D, hD, ?_⟩
  intro i j V p q hpq
  exact finiteTypeAcyclicDivisor_overlap_ideal f T _ _ V _ _ p q hpq s
    (D i) (D j) (hD i) (hD j)

end FLT.Mazur.CartierAbel
