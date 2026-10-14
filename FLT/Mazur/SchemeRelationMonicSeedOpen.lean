/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationMonicSeedQuotientCoverage
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# A propagated monic seed is an actual open of the original source

Monicity over the coefficient target forces equal seed coordinates whenever
propagated source coordinates agree. The original relation monomorphism then
forces equal arrows. Thus the propagated branch is itself monic; when etale,
it is an open immersion, with no further descent or coverage hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationMonicSeedKernel
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (w : A.left ⟶ T) (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left)
  [Mono (a ≫ w)] [Mono (pullback.lift p.left q.left h)]
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left a

include h in
/-- A propagated monic seed has no duplicate original source morphisms. -/
theorem branch_mono : Mono b := by
  constructor
  intro Y x y he
  have hh := congrArg (fun t ↦ t ≫ w) he
  have hs := seed_eq w h a x y (by simpa only [← Category.assoc] using hh)
  apply pullback.hom_ext
  · apply (cancel_mono (pullback.lift p.left q.left h)).mp
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst,
        SchemeRelationEtaleBranchPropagation.branch] using he
    · simpa only [Category.assoc, pullback.lift_snd, pullback.condition] using
        congrArg (fun t ↦ t ≫ a) hs
  · exact hs

include h in
/-- The two-sided etale seed propagates to a genuine open original-source selection. -/
theorem branch_isOpenImmersion [Etale p.left] [Etale a] : IsOpenImmersion b := by
  let _ := branch_mono w h a
  exact IsOpenImmersion.of_flat_of_mono b

variable [Etale p.left] [Etale a]

/-- The actual open of the original source reached by the seed orbit. -/
def sourceOpen : A.left.Opens := ⟨Set.range b, (b).isOpenMap.isOpen_range⟩

/-- Identify the propagated source with its actual open image as a scheme. -/
def sourceIso : pullback q.left a ≅ (sourceOpen (p := p) (q := q) a).toScheme := by
  let _ := branch_isOpenImmersion w h a
  exact IsOpenImmersion.isoOfRangeEq b (sourceOpen (p := p) (q := q) a).ι (by
    rw [Scheme.Opens.range_ι]; rfl)

@[reassoc]
theorem sourceIso_hom_ι : (sourceIso w h a).hom ≫ (sourceOpen (p := p) (q := q) a).ι = b := by
  let _ := branch_isOpenImmersion w h a
  exact IsOpenImmersion.lift_fac _ _ _

@[reassoc]
theorem sourceIso_inv_branch : (sourceIso w h a).inv ≫ b = (sourceOpen (p := p) (q := q) a).ι := by
  let _ := branch_isOpenImmersion w h a
  exact IsOpenImmersion.lift_fac _ _ _

end FLT.Mazur.SchemeRelationMonicSeedKernel
