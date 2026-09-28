# Deligne–Rapoport source ledger (FC08-C22)

Checked at 2026-09-28 20:32 UTC by HTTP GET, PDF text extraction and visual comparison
of the cited scan pages. This recovers citations; it supplies no Lean proofs.

## Sources and pagination

- **Primary [DR]:** P. Deligne and M. Rapoport, *Les schémas de modules de courbes
  elliptiques*, LNM 349 (1973), 143–316. [Bonn scan][dr]: HTTP 200, 174 PDF pages,
  linked by [Rapoport's publication list][list] (HTTP 200).
  SHA-256: `201e758341c69fc4cd635104b965a67beddaf93c295fbeea36ca37118e174864`.
  Here PDF pages are one-based: printed page = PDF page + 142; the first page is
  the title page. Chapter II starts at printed 173 / PDF 31.
- **Secondary [C]:** Conrad, *Arithmetic moduli of generalized elliptic curves*,
  [author's PDF][conrad] (HTTP 200), dated July 18, 2006; printed/PDF pages 4–6.
  Definitions 2.1.2, 2.1.4 and the attribution to DR II.1.12 were read.
- **Secondary [R]:** Conrad, *Modular curves and rigid-analytic spaces*,
  [author's PDF][rigid] (HTTP 200); Definition B.1.1, printed/PDF 46, was read.
  These are English restatements, not verbatim French DR quotations.
- **Independent [S]:** Stacks [0C46], [02KH], [0BY9], HTTP 200, HTML read today.
  No printed/PDF pagination claimed for these HTML sources.

Quotations below are French transcriptions of [DR], with typography and displayed
mathematics normalized. Explicitly marked excerpts omit text; paraphrases are not quotations.

## Definitions recovered from the primary source

**I.1.0, printed 160 / PDF 18:**
> Dans ce paragraphe, on appelle schéma en courbes sur un schéma S un morphisme
> propre et plat de présentation finie de dimension relative au plus 1.

English / C1: a scheme in curves is proper, flat, finitely presented, relative dimension ≤ 1.
**I.1.2, same page, excerpt:**
> De même, quand on parlera de courbes lisses, ou réduites, ou intègres,
> on sous-entendra "purement de dimension un".

English / C1: DR's smooth/reduced/integral curves implicitly have pure dimension one.

**II.1.1, printed 173 / PDF 31, definition excerpt:**
> Un polygone de Néron (resp. un n-gone) sur un corps algébriquement clos k est un
> schéma sur k isomorphe à l'un des polygones standards (resp. au n-gone standard).

English / C1: the standard n-gon, n ≥ 1, glues n copies of P¹ cyclically, identifying
0 on copy i with ∞ on copy i+1; over S it is obtained from the Z-model by base change.

**II, Définition 1.4, printed 175 / PDF 33:**
> Une courbe stable de genre un C sur un schéma S (ou espace algébrique S, ou champ
> algébrique S) est un schéma en courbes sur S (cf. I.1.0.) dont toute fibre géométrique
> est soit une courbe propre lisse et connexe de genre un soit un polygone de Néron.

English / C1–C2: every geometric fiber is a smooth proper connected genus-one curve or a polygon.

**II, Définition 1.12, printed 178 / PDF 36:**
> Une courbe elliptique généralisée (sur une base S) est une courbe stable de genre un
> p : C → S, munie d'un morphisme + : C^reg ×_S C → C tel que
> a) La restriction de (1.1 .1) à C^reg fait de C^reg un schéma en groupes commutatif.
> b) (1.12.1) définit une action du schéma en groupes C^reg sur C.
> c) Pour tout point géométrique s de S tel que C_s soit singulier, les translations
> y ↦ x+y de C_s (x ∈ C_s^reg(s)) agissent par rotations sur Γ(C_s).

English / C1 and G1-A: the smooth locus is a commutative group acting on the whole curve;
translations rotate the component graph of every singular geometric fiber.
The scan really prints `(1.1 .1)` in (a); the displayed morphism is numbered `(1.12.1)`.
C^reg denotes the relative smooth locus; [C] 2.1.4 writes it E^sm and explicitly names
its identity section e. A bare curve satisfying fiber conditions is not this group/action data.

## Numbered support for the fiber and cohomology gates

**I.1.1, printed 160 / PDF 18, excerpt:**
> On définit le genre arithmétique g_s de C_s par 1 − g_s = χ(C_s, O_{C_s}).

English / C2: DR uses arithmetic genus via Euler characteristic; g = dim H¹ requires
H⁰ = k and vanishing above degree one, as well as finite-dimensional cohomology.

**II, Lemme 1.2, printed 173 / PDF 31:**
> Soit C un polygone de Néron sur un corps algébriquement clos k.
> (i) H⁰(C, O_C) = k.
> (ii) H⁰(C, ω_C) est de dimension 1 sur k et le morphisme canonique
> H⁰(C, ω_C) ⊗_k O_C → ω_C est un isomorphisme. En particulier ω_C ≃ O_C.

English / C1–C2: polygons have constant global functions and trivial dualizing sheaf.
This H⁰(ω) statement is not an H¹(O) comparison without duality.

**II, Lemme 1.3, printed 174 / PDF 32:**
> Soit C une courbe réduite, connexe de genre un sur un corps algébriquement clos,
> ayant comme seules singularités de points doubles ordinaires et telle que ω_C ≃ O.
> Alors C est lisse ou un polygone de Néron.

English / C1–C2: the nodal characterization also requires trivial dualizing sheaf.
**Consequence for leaf 24:** nonempty, connected, reduced, pure dimension one, nodal
and arithmetic genus one alone do not assert DR II.1.4. For example, an elliptic
curve with a rational tail attached at one node has these properties but is not a
polygon or smooth. Use II.1.4's fiber classification, or prove the characterization
including ω ≃ O. This requirement is explicit in [C] 2.1.2 and [R] B.1.1 as well.

**II, Proposition 1.5, printed 175 / PDF 33, excerpt:**
> L'ensemble des points s ∈ S tel que C_s soit une courbe stable de genre un est
> un sous-schéma ouvert dans S.

English / C1: for p : C → S proper, flat and finitely presented (the stated hypothesis),
the stable-genus-one fiber locus is open; this is not itself the base-change theorem.

**II, Proposition 1.6, printed 175 / PDF 33:**
> Soit p : C → S une courbe stable de genre un.
> (i) p_* O_C = O_S universellement.
> (ii) ω_{C/S} et p_*(ω_{C/S}) sont inversibles et l'application canonique
> p^* p_*(ω_{C/S}) → ω_{C/S} est un isomorphisme.

English / C2–C3: global functions commute with all base changes and equal the base's
functions; the relative dualizing sheaf is pulled back from an invertible sheaf on S.
The **proof**, printed 176 / PDF 34, also states (excerpt):
> R¹p_* O est localement libre de formation compatible à tout changement de base S′ → S.

That is stronger than C3's field-extension target. It is not a substitute for constructing
Lean's actual cohomology and canonical tensor comparison. C3 can retain [S, 02KH],
Lemma 30.5.2 (flat base change), and [S, 0BY9], Lemma 53.8.2 (genus and H⁰ under
field extension). For arbitrary S′ → S, apply this to the residue-field extension
at each geometric fiber; do not assume the base morphism S′ → S is flat.

## The local node model (in Chapter I, not Chapter II)

**I, Proposition 5.3, printed 168 / PDF 26, conclusion excerpt:**
> Alors, le complété Ĉ_x de C en x est Ŝ_s-isomorphe à Ŝ_s[[X,Y]] / (XY−t)
> pour un t ∈ Γ(Ŝ_s, O) convenable.

Hypotheses read on the same page: p : C → S is a scheme in curves, S is Noetherian,
s ∈ S, x ∈ C_s(s), and C_s has an ordinary double point at x with rational tangents.
English / leaf 23: the completed family at a split rational node has equation XY = t.
For S = Spec k, k algebraically closed, this gives the completed local k-algebra
`Ô_{C,x} ≃ k[[X,Y]]/(XY)` at a node (t = 0).

**I, Théorème 5.3, printed 168–169 / PDF 26–27, first conclusion excerpt:**
> Alors, localement pour la topologie étale (au voisinage de x et s), C est
> S-isomorphe à X = S[u,v] / (uv−t) ⊂ A²_S pour t convenable.

Hypotheses: p : C → S is a scheme in curves, s ∈ S, x ∈ C_s(s) is an ordinary
double point; no Noetherian assumption is stated. The remaining sentence gives a
henselization comparison when tangents are rational over k(s).
English / leaf 23: after étale localization in source and base, a node is uv = t.
**Both the proposition and the theorem are printed “5.3”; distinguish them by kind.**
[S, 0C46] §53.19 independently gives the algebraically closed completed-ring criterion;
Definition 53.19.1 permits smooth points as well as nodes. Lemma 53.19.11 gives the
split-node criterion, and 53.19.12 its field-extension stability. These are Stacks
statements, not French DR quotations. The model applies to geometric fibers' closed
singular points, not to every point or to the completed local ring of the total space.

## Gate and leaf map; remaining work

| Source (printed / PDF pages) | Contract gate | FC08 leaf / remaining obligation |
| --- | --- | --- |
| I.1.0, I.1.2 (160 / 18) | C1 family and purity | 24: actual fiber predicates |
| II.1.1, II.1.4 (173, 175 / 31, 33) | C1–C2 exact fibers | 24: classification or equivalent |
| II.1.12 (178 / 36) | C1, G1-A group/action | Beyond 23/24; neither constructs the action |
| I, Prop./Thm.5.3 (168–169 / 26–27) | C1 nodes | 23: local rings/charts comparison |
| II.1.2–1.3 (173–174 / 31–32) | C1–C2 characterization | 24: retain trivial ω or classification |
| I.1.1; II.1.6 (160, 175–176 / 18, 33–34) | C2 genus; C3 H⁰ | 24: fibers; H¹ is later work |
| II.1.5 (175 / 33) | C1 open fiber locus | Optional support, not a 23/24 endpoint |
| 02KH, 0BY9; II.1.6 proof | C3 canonical comparison | Separate cohomology/base-change proofs |

Source recovery is complete for these statements. No Lean construction, equivalence,
finiteness proof, or C1/C2/C3 gate is declared discharged. C1's existing geometric
conditions are necessary but need the above strengthening for the full DR definition.

## Retrieval limitations

The [Springer chapter][springer] was accessible as subscription metadata; its
[PDF endpoint][springer-pdf] returned that HTML, not the chapter. The [preview] was
HTTP 200 but only two pages (title/contents). The complete primary text came from Bonn.
Earlier unsuccessful discovery: Springer `10.1007/BFb0066716` chapter/PDF and its
lowercase chapter variant returned 404; `10.1007/BFb0068683` was an unrelated Rudin
paper, including its redirected PDF endpoint. Conrad `papers/const.pdf` returned 404.
Google queries returned a JavaScript/CAPTCHA page; Bing returned unrelated results;
DuckDuckGo returned HTTP 202; IAS publication/faculty pages returned HTTP 403.
None of those responses supports a mathematical citation.

[dr]: https://www.math.uni-bonn.de/people/rapoport/myalggeom/preprints/Lesschemas.pdf
[list]: https://www.math.uni-bonn.de/people/rapoport/myalggeom/preprints.html
[conrad]: https://math.stanford.edu/~conrad/papers/kmpaper.pdf
[rigid]: https://math.stanford.edu/~conrad/papers/genpaper.pdf
[0C46]: https://stacks.math.columbia.edu/tag/0C46
[02KH]: https://stacks.math.columbia.edu/tag/02KH
[0BY9]: https://stacks.math.columbia.edu/tag/0BY9
[springer]: https://link.springer.com/chapter/10.1007/978-3-540-37855-6_4
[springer-pdf]: https://link.springer.com/content/pdf/10.1007/978-3-540-37855-6_4.pdf
[preview]: https://page-one.springer.com/pdf/preview/10.1007/978-3-540-37855-6_4
