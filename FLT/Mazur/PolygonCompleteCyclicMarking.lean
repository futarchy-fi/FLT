/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCartesianMarkings
public import FLT.Mazur.ConstantCyclicRelativeClosed

/-!
# The finite cyclic marking scheme of the complete family

On every specified cartesian square the original labels embed the constant
rank-n etale scheme into the whole family. This constructs a finite marking
scheme, without presupposing a group law on the smooth locus of the family.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S Y : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- The original marking, indexed by its cyclic residue, as a section over the base. -/
def completeCyclicSection (a : ZMod n) : 𝟙_ (Over S) ⟶ Over.mk q :=
  Over.homMk (completeCartesianMarking K n h s p q hs ((ZMod.finEquiv n).symm a))
    (completeCartesianMarking_snd K n h s p q hs _)

/-- The actual finite constant marking scheme mapped into the complete family. -/
def completeCyclicMarking : ConstantCyclicGroup.model S n ⟶ Over.mk q :=
  Sigma.desc (completeCyclicSection K n h s p q hs)

/-- Each component is exactly the prescribed original section. -/
@[reassoc (attr := simp)] theorem completeCyclicMarking_component (a : ZMod n) :
    ConstantCyclicGroup.component S n a ≫ completeCyclicMarking K n h s p q hs =
      completeCyclicSection K n h s p q hs a := Sigma.ι_comp_desc _ _

/-- The actual section labels stay distinct over every nonempty test scheme. -/
theorem completeCyclicSection_universallyDistinct :
    UniversallyDistinctSections.UniversallyDistinct (completeCyclicSection K n h s p q hs) := by
  intro V g hV a b he
  obtain ⟨x⟩ := hV
  by_contra hab
  have hij : (ZMod.finEquiv n).symm a ≠ (ZMod.finEquiv n).symm b :=
    fun hi ↦ hab ((ZMod.finEquiv n).symm.injective hi)
  have hx := congrArg (fun f ↦ f.left x) he
  exact Set.disjoint_left.mp (completeCartesianMarkings_pairwise K n h s p q hs hij)
    ⟨g.left x, rfl⟩ ⟨g.left x, hx.symm⟩

/-- The constant marking scheme is a closed subscheme of the actual whole family. -/
theorem completeCyclicMarking_closed :
    IsClosedImmersion (completeCyclicMarking K n h s p q hs).left := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  let _ : IsSeparated (Over.mk q).hom := inferInstanceAs (IsSeparated q)
  apply ConstantCyclicRelativeClosed.closed
  simpa only [completeCyclicMarking_component] using
    completeCyclicSection_universallyDistinct K n h s p q hs

/-- Its actual kernel retains the product of every original marking ideal. -/
theorem completeCyclicMarking_kernel :
    (completeCyclicMarking K n h s p q hs).left.ker =
      ∏ i : Fin n, (completeCartesianMarking K n h s p q hs i).ker := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  let _ : IsSeparated (Over.mk q).hom := inferInstanceAs (IsSeparated q)
  have hd := completeCyclicSection_universallyDistinct K n h s p q hs
  have hd' : UniversallyDistinctSections.UniversallyDistinct (fun a : ZMod n ↦
      ConstantCyclicGroup.component S n a ≫ completeCyclicMarking K n h s p q hs) := by
    simpa only [completeCyclicMarking_component] using hd
  rw [ConstantCyclicRelativeClosed.kernel_eq_component_product _ hd']
  simp only [completeCyclicMarking_component, completeCyclicSection, Over.homMk_left]
  exact Equiv.prod_comp (ZMod.finEquiv n).symm.toEquiv
    (fun i ↦ (completeCartesianMarking K n h s p q hs i).ker)

/-- The marking carrier has scheme-theoretic rank n over the arbitrary base. -/
theorem completeCyclicMarking_degree :
    FCurve.FiniteLocallyFreeDegree (ConstantCyclicGroup.model S n).hom n :=
  ConstantCyclicRelativeGeometry.degree S n

/-- The original marking carrier remains etale in every characteristic. -/
theorem completeCyclicMarking_etale : Etale (ConstantCyclicGroup.model S n).hom :=
  ConstantCyclicRelativeGeometry.etale S n

end FLT.Mazur.PolygonInfinitesimalStages
