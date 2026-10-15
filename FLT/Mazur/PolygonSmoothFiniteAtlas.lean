/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothLocus

/-!
# The finite labeled scheme atlas of a specified polygon

Keep the original normalization coordinates while presenting the smooth
polygon as a coproduct of schemes indexed by Fin n. This is the same index
and coefficient convention as the actual arithmetic resolved atlas.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  [LocallyOfFinitePresentation C.hom]
local notation "torus" => Spec (CommRingCat.of (LaurentPolynomial K))

/-- The original full Laurent chart with its original finite component label. -/
def smoothFiniteChart (i : Fin n) : torus ⟶ C.hom.smoothLocus.toScheme :=
  (smoothComponent K n hn p q h (ZMod.finEquiv n i)).left

instance smoothFiniteChart_isOpenImmersion (i : Fin n) :
    IsOpenImmersion (smoothFiniteChart K n hn p q h i) :=
  inferInstanceAs (IsOpenImmersion (smoothComponent K n hn p q h _).left)

/-- The finite chart retains the original full normalization morphism. -/
@[reassoc] theorem smoothFiniteChart_inclusion (i : Fin n) :
    smoothFiniteChart K n hn p q h i ≫ C.hom.smoothLocus.ι =
      (torusToComponent K ≫ componentι K n i ≫ p).left := by
  rw [smoothFiniteChart, smoothComponent_ι, RingEquiv.symm_apply_apply]

/-- The finite chart retains the original coefficient map. -/
@[reassoc] theorem smoothFiniteChart_structure (i : Fin n) :
    smoothFiniteChart K n hn p q h i ≫ C.hom.smoothLocus.ι ≫ C.hom =
      (MultiplicativeGroupScheme.gm K).hom :=
  (smoothComponent K n hn p q h (ZMod.finEquiv n i)).w

/-- The full finite Laurent coproduct maps into the original smooth polygon. -/
def smoothFiniteAtlasMap : (∐ fun _ : Fin n => torus) ⟶ C.hom.smoothLocus.toScheme :=
  Sigma.desc (smoothFiniteChart K n hn p q h)

/-- Each coproduct leg is exactly its original normalized component. -/
@[reassoc] theorem smoothFiniteAtlasMap_chart (i : Fin n) :
    Sigma.ι (fun _ : Fin n => torus) i ≫ smoothFiniteAtlasMap K n hn p q h =
      smoothFiniteChart K n hn p q h i := Sigma.ι_comp_desc _ _

instance smoothFiniteAtlasMap_isOpenImmersion :
    IsOpenImmersion (smoothFiniteAtlasMap K n hn p q h) := by
  apply isOpenImmersion_sigmaDesc
  intro i j hij
  exact TopologicalSpace.Opens.coe_disjoint.mpr
    (smoothComponent_disjoint K n hn p q h ((ZMod.finEquiv n).injective.ne hij))

instance smoothFiniteAtlasMap_isIso : IsIso (smoothFiniteAtlasMap K n hn p q h) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply TopologicalSpace.Opens.ext
  apply Set.eq_univ_of_forall
  intro z
  have hz : z ∈ ⨆ i, (smoothComponent K n hn p q h i).left.opensRange := by
    rw [smoothComponent_cover]
    trivial
  obtain ⟨i, x, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  refine ⟨Sigma.ι (fun _ : Fin n => torus) ((ZMod.finEquiv n).symm i) x, ?_⟩
  have he := congrArg (fun f => f x)
    (smoothFiniteAtlasMap_chart K n hn p q h ((ZMod.finEquiv n).symm i))
  simp only [smoothFiniteChart, RingEquiv.apply_symm_apply] at he
  exact he.trans hx

/-- The finite atlas is the entire original smooth polygon as a scheme. -/
def smoothFiniteAtlasIso : (∐ fun _ : Fin n => torus) ≅ C.hom.smoothLocus.toScheme :=
  asIso (smoothFiniteAtlasMap K n hn p q h)

/-- The whole atlas preserves the original field structure. -/
@[reassoc] theorem smoothFiniteAtlasMap_structure :
    smoothFiniteAtlasMap K n hn p q h ≫ C.hom.smoothLocus.ι ≫ C.hom =
      Sigma.desc (fun _ : Fin n => (MultiplicativeGroupScheme.gm K).hom) := by
  apply Sigma.hom_ext
  intro i
  rw [smoothFiniteAtlasMap_chart_assoc, Sigma.ι_comp_desc]
  exact smoothFiniteChart_structure K n hn p q h i

end FLT.Mazur.PolygonPinching
