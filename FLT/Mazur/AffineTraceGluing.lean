/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTraceCharts

/-!
# Gluing traces over the whole target

Local traces for unrelated finite bases glue in the original structure sheaf.
The result agrees with every finite free chart and is independent of the cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineTraceGluing
open AffineTraceCharts
universe u v w
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [IsAffine Y]

/-- Arbitrary finite free charts have the same traces on their overlap. -/
theorem chart_overlap (U V : Y.affineOpens)
    (hU : AffineOpenNorm.HasBasis f U) (hV : AffineOpenNorm.HasBasis f V)
    (s : Γ(X, ⊤)) :
    Y.presheaf.map (homOfLE inf_le_left).op (chart f U hU s) =
      Y.presheaf.map (homOfLE inf_le_right).op (chart f V hV s) := by
  let W : Y.affineOpens := ⟨U.1 ⊓ V.1, U.2.inf V.2⟩
  have h₁ : W ≤ U := show U.1 ⊓ V.1 ≤ U.1 from inf_le_left
  have h₂ : W ≤ V := show U.1 ⊓ V.1 ≤ V.1 from inf_le_right
  have hW := hU.restrict f h₁
  exact (chart_restrict f hU hW h₁ s).trans
    (chart_restrict f hV hW h₂ s).symm

variable {ι : Type v} (U : ι → Y.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis f (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

include hcover in
/-- Each local multiplication trace glues uniquely in the original sheaf. -/
theorem existsUnique_trace (s : Γ(X, ⊤)) :
    ∃! t : Γ(Y, ⊤), ∀ i,
      Y.presheaf.map (homOfLE le_top).op t = chart f (U i) (hU i) s := by
  exact Y.sheaf.existsUnique_gluing' (fun i ↦ (U i).1) ⊤
    (fun _ ↦ homOfLE le_top) (ge_of_eq hcover) (fun i ↦ chart f (U i) (hU i) s)
    (fun i j ↦ chart_overlap f (U i) (U j) (hU i) (hU j) s)

/-- The global trace supplied by the structure sheaf, with no chosen global basis. -/
def trace (s : Γ(X, ⊤)) : Γ(Y, ⊤) :=
  (existsUnique_trace f U hU hcover s).choose

/-- Every chosen chart recovers its actual trace. -/
theorem trace_chart (s : Γ(X, ⊤)) (i : ι) :
    Y.presheaf.map (homOfLE le_top).op (trace f U hU hcover s) =
      chart f (U i) (hU i) s :=
  (existsUnique_trace f U hU hcover s).choose_spec.1 i

/-- Equality with a trace is detected on the entire chosen cover. -/
theorem eq_trace (s : Γ(X, ⊤)) (t : Γ(Y, ⊤))
    (ht : ∀ i, Y.presheaf.map (homOfLE le_top).op t = chart f (U i) (hU i) s) :
    t = trace f U hU hcover s :=
  (existsUnique_trace f U hU hcover s).choose_spec.2 t ht

/-- Any additional finite free chart computes the same global trace. -/
theorem trace_any_chart (V : Y.affineOpens) (hV : AffineOpenNorm.HasBasis f V)
    (s : Γ(X, ⊤)) :
    Y.presheaf.map (homOfLE le_top).op (trace f U hU hcover s) =
      chart f V hV s := by
  apply Y.sheaf.eq_of_locally_eq' (fun i ↦ V.1 ⊓ (U i).1) V.1
    (fun _ ↦ homOfLE inf_le_left) (by rw [← inf_iSup_eq, hcover, inf_top_eq])
  intro i
  let W : Y.affineOpens := ⟨V.1 ⊓ (U i).1, V.2.inf (U i).2⟩
  have hWV : W ≤ V := show V.1 ⊓ (U i).1 ≤ V.1 from inf_le_left
  have hWU : W ≤ U i := show V.1 ⊓ (U i).1 ≤ (U i).1 from inf_le_right
  have hW := hV.restrict f hWV
  change Y.presheaf.map (homOfLE hWV).op
    (Y.presheaf.map (homOfLE le_top).op (trace f U hU hcover s)) =
      Y.presheaf.map (homOfLE hWV).op (chart f V hV s)
  rw [chart_restrict f hV hW hWV]
  have hi := congrArg (Y.presheaf.map (homOfLE hWU).op)
    (trace_chart f U hU hcover s i)
  rw [chart_restrict f (hU i) hW hWU] at hi
  simp only [← CommRingCat.comp_apply, ← Functor.map_comp] at hi ⊢
  convert hi using 2

/-- All traces are independent of the entire finite free cover and its bases. -/
theorem trace_independent {κ : Type w} (V : κ → Y.affineOpens)
    (hV : ∀ j, AffineOpenNorm.HasBasis f (V j)) (hcoverV : ⨆ j, (V j).1 = ⊤)
    (s : Γ(X, ⊤)) :
    trace f U hU hcover s = trace f V hV hcoverV s := by
  apply eq_trace
  intro j
  exact trace_any_chart f U hU hcover (V j) (hV j) s

end FLT.Mazur.AffineTraceGluing
