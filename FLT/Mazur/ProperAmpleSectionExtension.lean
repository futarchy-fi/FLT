/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleChartSectionExtension
public import FLT.Mazur.ProperAmpleSectionAffineUnrestricted
public import FLT.Mazur.TensorPowerNestedSection

/-!
# Original section numerators over arbitrary proper affine bases

Add a power of the specified section to a finite affine ample cover. The
existing denominator-clearing and gluing theorem extends every function on
its generator open. Flattening the actual nested power retains that section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback SectionCover
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X S : Scheme} [IsAffine S] (f : X ⟶ S) [IsProper f]
  {L : X.Modules}

include f in
/-- Every function on an ample section open has a numerator in its original tensor powers. -/
theorem exists_ampleSection_numerator_unrestricted (hA : AmpleLineBundle L)
    (z : Γ(L, ⊤)) (a : Γ(X, sectionGeneratorOpen L z)) :
    ∃ (m : ℕ) (t : Γ(tensorPower L m, ⊤)),
      (tensorPower L m).presheaf.map (sectionGeneratorOpen L z).leTop.op t =
        a • tensorPowerSection L (sectionGeneratorOpen L z)
          (L.presheaf.map (sectionGeneratorOpen L z).leTop.op z) m := by
  obtain ⟨ι, hι, d, hd, s, haff, hcover⟩ := hA.common_degree_section_cover
  let _ := hι
  let s' : ι ⊕ Unit → Γ(tensorPower L d, ⊤) :=
    Sum.elim s (fun _ ↦ tensorPowerSection L ⊤ z d)
  have haff' : ∀ i, IsAffineOpen (chart s' i) := by
    intro i
    rcases i with i | u
    · exact haff i
    · exact hA.isAffineOpen_powerSection_unrestricted f d hd _
  have hcover' : ⨆ i, chart s' i = ⊤ := by
    apply top_unique
    rw [← hcover]
    exact iSup_le (fun i ↦ le_iSup (chart s') (Sum.inl i))
  have hV : chart s' (Sum.inr ()) = sectionGeneratorOpen L z :=
    tensorPowerSection_generatorOpen hA.2.1 z hd
  have hex := sectionCover_extension s' haff' hcover' (Sum.inr ())
  rw [hV] at hex
  obtain ⟨N, t, ht⟩ := hex a
  refine ⟨d * N, (tensorPowerMulIso L d N).hom.app ⊤ t, ?_⟩
  have hn := congrArg (fun k ↦ k t)
    ((tensorPowerMulIso L d N).hom.mapPresheaf.naturality
      (sectionGeneratorOpen L z).leTop.op)
  change (tensorPowerMulIso L d N).hom.app (sectionGeneratorOpen L z)
    ((tensorPower (tensorPower L d) N).presheaf.map
      (sectionGeneratorOpen L z).leTop.op t) =
      (tensorPower L (d * N)).presheaf.map (sectionGeneratorOpen L z).leTop.op
        ((tensorPowerMulIso L d N).hom.app ⊤ t) at hn
  rw [← hn]
  erw [ht, Hom.app_smul]
  congr 1
  dsimp only [powerFrame, s', Sum.elim_inr]
  rw [tensorPowerSection_restrict, tensorPowerMulIso_powerSection]
  rfl

end FLT.Mazur.FCurve
