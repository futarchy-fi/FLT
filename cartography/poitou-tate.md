# Poitou–Tate duality: FLT dependency map

Scope: read-only inspection of /Users/kas/FLT (blueprint LaTeX, FLT/Assumptions/, and Lean
sources), plus the checked-in Mazur cartography/panel branches. No network lookup was used.
Exact theorem-number citations below are marked (literature-verify) when based on standard
references rather than a local copy of the literature.

## 1. What the repository says, and every consumer

### Auditable invocation sites

| file:line | text/fact | consequence |
|---|---|---|
| blueprint/src/chapter/chtopbestiary.tex:31-36 | Defines continuous Hᶦ(G_K,M) for K/ℚₚ, with M a discrete G_K-module, via continuous cocycles, finite quotients, or étale cohomology. | The arithmetic cohomology object must cover local absolute Galois groups, not only abstract discrete groups. |
| chtopbestiary.tex:38-59 | For finite M, local Hᶦ is finite; Hᶦ=0 for i>2 for torsion M; H²(G_K,μₙ)≅ℤ/n and H²(K,μ∞)≅ℚ/ℤ. | Local finiteness, cohomological dimension two, and the invariant map precede local duality. |
| chtopbestiary.tex:67-77 | The local Tate/Poincaré pairing Hᶦ(G_K,M) × H²⁻ᶦ(G_K,M′) → ℚ/ℤ is perfect, followed by Euler–Poincaré. | Local input to Selmer/Poitou–Tate. |
| chtopbestiary.tex:79-94 | Global CFT and the Skinner–Wiles prescribed-local-extension trick are stated. | CFT is upstream, but these lines do not state finite-module Poitou–Tate. |
| chtopbestiary.tex:96 | “We also need Poitou-Tate duality … we don't even have Galois cohomology in Lean yet.” | Explicit blueprint node; no theorem body or dependency edges are supplied. |
| blueprint/src/chapter/ch03freyold.tex:274-285 | The ℓ-adic finite-flat assertion uses fppf cohomology (or Katz–Mazur elementary arguments). | Local finite-flat/fppf cohomology is a sibling dependency, not itself a global PT invocation. |
| FLT/Assumptions/README.md:65-68 | Says arithmetic Galois cohomology is missing and lists “Poitou-Tate (aka the Greenberg-Wiles long exact sequence)”. | PT is intended as an assumption once the cohomology API exists. |
| FLT/Assumptions/Mazur.lean:41-45 | Mazur's 154-page Eisenstein-quotient descent uses Grothendieck cohomology theories. | The one-line Mazur axiom hides the D6a descent stack. |
| FLT/GlobalLanglandsConjectures/GLzero.lean:22-27 | Wiles' R=T proof used CFT “in the form of global Tate duality” centrally. | Direct spine consumer: deformation/Selmer numerical arguments need global duality. |
| FLT.lean:156-160 | Publicly imports continuous representations, ContCohomology.Basic, and ContCohomology.CupProduct. | Generic cohomology/cup products exist; number-field local/global duality does not. |

Name-only or non-consumer hits: FLT/Assumptions/Odlyzko.lean:23,45 and
blueprint/src/chapter/ch03freyreduction.tex:272-275 use “Poitou” only for the Odlyzko
discriminant-bound citation; they are not Poitou–Tate. An rg search finds no Selmer declaration
or invocation in /Users/kas/FLT.

### Hidden consumers recovered from the Mazur panel

The panel branch records the missing edges explicitly: panel/mazur-dependency:82-83,114-123
and panel/mazur-adjudication:30-35 add global CFT, Poitou–Tate, and Selmer machinery to both
D6 prongs. The reconciled map identifies D6a/D6b and their downstream D7b/D8/D9/W chain
(cartography/mazur-reconciled.md:241-259; closure at panel/mazur-dependency:82-88).

1. **D6a, Mazur/Eisenstein quotient (direct, hub-lsb1u.2).** Descent to a finite
   Mordell–Weil group uses finite-flat/Raynaud/Cartier-dual objects, finite generic-fibre
   Galois modules, and global Selmer control. The natural fields are ℚ and cyclotomic or
   auxiliary number fields in the Eisenstein calculation; local conditions are unramified
   outside the bad set and finite-flat at the residual characteristic. A finite-module PT
   theorem is sufficient only after a finite-flat/fppf-to-Galois comparison at bad places.
2. **D6b, winding quotient (direct, hub-lsb1u.2).** Kolyvagin–Logachev/Gross–Zagier (or
   Kato) gives the rank-zero step for a modular abelian quotient. Modules are finite pⁿ-torsion
   subquotients of its Tate module and Cartier/Weil duals, over ℚ and Heegner/auxiliary
   fields. PT supplies Selmer exactness, local-condition orthogonality, and the
   Euler-system-to-Mordell–Weil rank control; if the deep theorem is imported wholesale,
   only its theorem interface is needed.
3. **D7b → D8 → D9 → W (transitive Mazur consumers).** These consume the rank-zero quotient
   from D6a or D6b; they do not call PT separately. W itself is only the torsion statement,
   so PT is not needed merely to state W.
4. **B2/C1–C4 (latent 2-descent consumers).** Honest per-curve descent requires E[2]-Selmer
   groups and local solubility over ℚ, with S containing 2, infinity, and bad primes. This
   is absent from current source but is a real PT edge if those descents are formalized.
5. **Spine/Wiles R=T (direct, GLzero.lean:26-27).** The weakest useful interface is global
   Tate/PT duality for finite residual and adjoint modules with the selected local conditions
   and the Selmer/dual-Selmer dimension formula. A full nine-term theorem is reusable;
   a fixed R=T proof may consume only its Selmer corollary.
6. **Frey/ch03 local layer (cohomology consumer, not full-PT).** Tate-curve, Hilbert-90/Kummer,
   and finite-flat arguments at 2 and ℓ need local H¹ and local duality/finite-flat comparison
   (ch03freyold.tex:264-285). The current everywhere-unramified-character route uses
   Minkowski (ch03freyold.tex:347-352), not PT; replacing it by CFT/Selmer adds a new PT edge.
7. **Mazur_statement is not a Lean consumer.** Its only declaration is
   FLT/Assumptions/Mazur.lean:105-106; FreyPackage.mazur is discharged by knownin1980s at
   FLT/FreyCurve/Mazur.lean:30-36. PT is hidden in the proposed D6 proof route, not today's
   axiom invocation.

## 2. Weakest sufficient package for FLT

Let K be a number field, S a finite set containing infinity, all primes over the residue
characteristics of finite M, and all ramified places, and G_{K,S}=Gal(K_S/K). Put
Mᴰ = Hom(M, μ∞) = M∨(1), with the action explicit. The safe minimum is:

* **Local-only ch03/B5:** finite discrete G_{Kᵥ}-modules, local H¹, Kummer/Hilbert 90, and
  the perfect Hᶦ × H²⁻ᶦ Tate pairing. No global nine-term sequence.
* **D6a/D6b and honest 2-descent:** finite discrete G_{K,S}-modules, local Tate pairings,
  unramified local subgroups, and PT exactness/orthogonality for those local conditions.
  The finite-flat/fppf condition at v|p needs a separate bridge or fppf duality.
* **Wiles R=T:** the same package restricted to the residual/adjoint modules and deformation
  conditions actually used; expose the Selmer/dual-Selmer dimension formula, rather than
  forcing each consumer to manipulate every nine-term map.

The robust reusable upper bound is the finite-S nine-term sequence:

    0 → H⁰(G_{K,S},M) → ⊕v∈S H⁰(Kᵥ,M) → H²(G_{K,S},Mᴰ)∨
      → H¹(G_{K,S},M) → ⊕v∈S H¹(Kᵥ,M) → H¹(G_{K,S},Mᴰ)∨
      → H²(G_{K,S},M) → ⊕v∈S H²(Kᵥ,M) → H⁰(G_{K,S},Mᴰ)∨ → 0.

Here A∨=Hom_cont(A,ℚ/ℤ), with the standard archimedean modifications. In the all-places
form, degree one is a restricted product with respect to unramified subgroups. For local
conditions L=(Lᵥ), the needed corollary is PT control and orthogonality
Lᵥ⊥=Lᵥᴰ, comparing H¹_L(K,M) with H¹_L⊥(K,Mᴰ). This Selmer corollary, not every
nine-term term, is the weakest statement needed by a fixed R=T or Euler-system consumer.

## 3. Number-field Galois-cohomology statement inventory

Grades are incremental cost in this repository (S < M < L < XL), not proof closure.
Theorem/section numbering is (literature-verify).

1. **Continuous arithmetic cohomology — S.** For a field K and continuous discrete
   G_K-module M, define Hᶦ(K,M)=Hᶦ_cont(G_K,M), functorially in K, M, and restriction to
   Kᵥ. Citation: NSW, Ch. I §§1-2; Milne ADT, I.1 (literature-verify). Repo anchors:
   FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean:19-23 and
   GaloisRep.lean:17-21.
2. **Local finiteness and cd=2 — M.** For finite Kᵥ/ℚₚ and finite M, all Hᶦ(Kᵥ,M)
   are finite, Hᶦ=0 for i>2, and H²(Kᵥ,μ∞)≅ℚ/ℤ. Citation: Serre, Galois Cohomology,
   Ch. II §5, Props. 14-15 (the blueprint cites these at chtopbestiary.tex:38-65);
   Milne ADT, I.2 (literature-verify).
3. **Local Tate duality — L.** For finite M, cup product and the local invariant give
   perfect Hᶦ(Kᵥ,M) × H²⁻ᶦ(Kᵥ,Mᴰ) → ℚ/ℤ pairings for 0≤i≤2, with real/complex
   corrections. Citation: Serre, Galois Cohomology, Ch. II §5, Thm. 2; Milne ADT, I.2
   (literature-verify); explicit blueprint formulation at chtopbestiary.tex:67-73.
4. **Global compact-support duality — L.** For number field K, finite S, and finite M,
   compactly supported Hᶦ_c(G_{K,S},M) is dual to H³⁻ᶦ(G_{K,S},Mᴰ) through the sum
   of local invariants. Citation: Milne ADT, I.4 (Theorem 4.10) and NSW, Ch. VIII §8.6
   (literature-verify). This is the precise global form behind “global Tate duality” in
   GLzero.lean:26-27.
5. **Poitou–Tate nine-term exactness — XL.** Under the hypotheses above, the nine-term
   sequence in §2 is exact, including localization and the final dual H⁰ term; equivalently
   use its restricted-product all-places form. Citation: NSW, Ch. VIII §8.6, especially
   Thm. 8.6.7; Milne ADT, I.4-I.6 (literature-verify). The assumptions README names this
   the “Greenberg–Wiles long exact sequence”.
6. **Selmer orthogonality/control — L.** For local conditions Lᵥ⊂H¹(Kᵥ,M), define
   H¹_L(K,M) and dual Lᵥᴰ⊂H¹(Kᵥ,Mᴰ); PT identifies the annihilator of the global Selmer
   image with the dual Selmer image and gives the finite dimension/Euler characteristic
   formula. Citation: NSW, Ch. VIII §8.7; Milne ADT, I.6; Greenberg-Wiles, Cohen–Lenstra
   heuristics and 2-class groups (the Greenberg-Wiles formula), all (literature-verify).
7. **Finite-flat/fppf local-condition bridge — XL.** For finite flat commutative G/Rᵥ,
   relate H¹_fppf(Rᵥ,G) to generic-fibre G_{Kᵥ}-cohomology, compatibly with Cartier duality
   and local Tate pairings. Away from the residue characteristic this reduces to finite étale
   (Galois) cohomology; at v|p it does not. Citation: Milne ADT, III; Artin-Milne duality
   (literature-verify). Repo status: only a comment seed at
   FLT/GroupScheme/FiniteFlat.lean:5-15 and fppf use at ch03freyold.tex:274-285.
8. **Local-global compatibility/restricted products — L.** Localization is continuous,
   unramified outside S, and lands in the restricted product of H¹(Kᵥ,M); cup products and
   invariant maps sum compatibly with global reciprocity. Citation: Milne ADT, I.4-I.6;
   NSW, Ch. VIII §8.6 (literature-verify). This is where CFT/idele topology meets PT.
9. **Euler characteristic/dimension corollary — M.** For finite M, alternating orders
   (or dimensions over a coefficient field) of global, local, and dual Selmer groups satisfy
   the PT Euler–Poincaré formula used in deformation rings and rank-zero arguments. Citation:
   NSW, Ch. VIII §8.7; Milne ADT, I.5; local prototype at chtopbestiary.tex:75-77
   (literature-verify).

## 4. Dependency edges and the exact CFT boundary

* **CFT hub-lsb1u.9 → nodes 2-4, 8.** The upstream CFT package should provide local/global
  reciprocity, invᵥ:Br(Kᵥ)→ℚ/ℤ, the global sum-of-invariants/product formula, Kummer
  identifications used in H¹, and idele/adele restricted-product topology. Blueprint:
  chtopbestiary.tex:79-94.
* **CFT boundary.** Stop the CFT bead after reciprocity/invariant maps and the Gₘ/Brauer
  duality they prove. **Poitou–Tate begins** when one passes to an arbitrary finite G_{K,S}-module
  M, forms Mᴰ, proves local Tate duality for M, and proves localization exactness/orthogonality.
  Do not count nine-term exactness as CFT output unless hub-lsb1u.9 explicitly exports it.
* **Nodes 2-6, 8-9 → spine/Wiles R=T.** GLzero.lean:26-27 is the only direct repo statement;
  consume the finite residual/adjoint Selmer corollary (node 6) and numerical formula (node 9).
* **Nodes 3, 5-8 → Mazur hub-lsb1u.2/D6a.** Add finite-flat comparison at p,
  unramified/finite-flat local conditions, cyclotomic/Cartier duals, and class-group input.
  Then D6a → D7b → D8 → D9 → W; D7b-W do not independently consume PT.
* **Nodes 3, 5-6, 8-9 → Mazur hub-lsb1u.2/D6b.** Add self-dual pⁿ-torsion of the
  winding quotient, Heegner/Euler-system local conditions, and the analytic-to-algebraic
  rank theorem; import Kolyvagin–Logachev/Kato as an external edge if not formalized.
* **Nodes 1-3, 6-8 → B2/C1-C4 (latent).** Honest 2-descent needs M=E[2], its Weil dual,
  S⊃{2,infinity,bad}, local solubility, and Selmer control. Current source has no Selmer
  symbol; this edge comes from the repaired Mazur panel.
* **Nodes 1-3, 7 → ch03/B5.** Local Kummer/Hilbert 90 and finite-flat comparison feed
  Tate-curve/flat arguments. The current Minkowski character step is not a PT edge; a CFT
  replacement would add CFT → PT → A5.

### Mathlib/repo anchors

* Mathlib's Mathlib.RepresentationTheory.Homological.ContCohomology.Basic defines continuous
  cohomology as homology of homogeneous cochains and leaves long exact sequences as TODO
  (/Users/kas/FLT/.lake/packages/mathlib/Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean:15-18,38-41).
* FLT extends it with coinduced resolutions, cocycle/coboundary kernels, and
  ContinuousCohomology.cohomologyIsoQuot (FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean:15-36,212-240),
  and cup products descending to cohomology (…/CupProduct.lean:17-20,32-45,567-584).
  These are foundations for cup-pairing proofs, not arithmetic local/global duality.
* AbsoluteGaloisGroup.lean:19-23,48-76 supplies continuous absolute-Galois groups and maps;
  GaloisRep.lean:17-21,47-52 supplies continuous linear representations; FLT/Mathlib/FieldTheory/Galois/Infinite.lean:23-50
  supplies the finite continuous G-set/finite étale algebra bridge.
* EllipticCurve/Torsion.lean:31-52,99-108 and KnownIn1980s/EllipticCurves/WeilPairing.lean:14-19,36-42
  are intended E[n], Galois-action, and Weil-pairing anchors, but key results are sorry.
  GroupScheme/FiniteFlat.lean:5-15 is only a design comment.
* NumberField/AdeleRing.lean:28-37 develops adeles/base change, not cohomological restricted
  products or reciprocity. Thus Assumptions/README.md:65-68 remains accurate for arithmetic
  Galois cohomology despite generic continuous-cohomology imports.

## 5. Route risks and size verdict

* **Convention risk:** fix G_{K,S}, Mᴰ=M∨(1), archimedean terms, S, and restricted-product
  topology before writing Lean. “Global Tate duality” is otherwise too ambiguous to type-check.
* **Finite-flat risk:** ordinary Galois PT does not identify the finite-flat condition at v|p.
  D6a and ch03 need an fppf/finite-flat duality bridge or an imported theorem.
* **Route risk:** D6a and D6b are both XL+ closure in the Mazur panel
  (cartography/panel/mazur-adjudication.md:39-43). PT is shared infrastructure, not a cheap
  substitute for the 150-page descent or the Gross–Zagier/Kolyvagin stack.
* **Import-wholesale option:** if CFT, finite-flat duality, and D6 are assumptions, expose only
  nodes 5-6 and 9 as the PT interface. If proved, the reusable finite-module PT plus its
  finite-flat extension is XL standalone and the Mazur/Wiles transitive closure XL+.
  There is no honest S/M route in this repository.

**Size verdict:** build a finite-discrete G_{K,S} PT/Selmer API first (reusable by Wiles, Mazur,
and 2-descent), then a separately named finite-flat/fppf extension; budget combined Mazur closure
as XL+.
