# Editorial audit of preprint 1.0

Verdict: **EDITORIALLY_READY**, subject to the artifact checks recorded in the release audit. The mathematical statements are
stable: the last changes to the manuscript were the author's third editorial round and the round-5 corrections.

## English edition
The edited manuscript was prepared from the research draft 7.14 with the mathematical content locked; every change to a statement,
constant or proof step came from a recorded audit finding. The editorial report (`02_validation/EDITORIAL_REPORT.md`) lists the
passes:
1. the editorial pass toward Random Structures & Algorithms, in the voice of the Latinon preprint 1.0, with American spelling and the
   series conventions for references, statement heads and locators;
2. the author's ten observations of 17 November 2026 (abstract, scope of the literature search, Sections 1.1 and 1.5, Remark 4.3,
   Steps 4–5, openers of Sections 5.8–6, the Nash-Williams parenthesis, the tower threshold, Section 7 and the open problems);
3. the author's second review (clarity of Corollary 1.4, Steps 6–7 of Section 4.2, the rounding in (5.1), Lemmas 5.8, 5.8′ and
   5.19; style items A–E: numerical notes pruned except the comparison 3.3 against 24 and the torsion, the abstract's last sentence
   split, varied sentence openers, Section 1.2, Open problem 2);
4. two tables and one figure, kept only where they support the narrative: Table 1 (counting results), Figure 1 (vortex schematic)
   and Table 2 (order of the constants);
5. the corrections of the audit rounds;
6. the author's second editorial round (abstract split into shorter sentences, a shorter index paragraph in §1.1, the sentence
   after Corollary 1.11, the opening of §6, varied deductive openers in place of "So"), with four precision adjustments kept from
   the locked text or the audit (the type law of a uniformly random triple; the full type law P; the definition of the outline;
   "feasible counts" and the class proportions), and no serial commas, as in the rest of the series;
7. the Lean formalization, first as Section 1.7 and, after the third round, as one paragraph "Formal verification" that points to the formal companion, as in the CDR and Nash-Williams papers;
8. the author's third editorial round: series framing in the front block and abstract (Paper I, the research note, this Paper II), Table 2 with the five settings of the scheme, Acknowledgments and Use of artificial intelligence with the text of CDR III unchanged, and a prose pass against generic patterns in which the author's own sentences were kept.
The four suspected extraction errors reported by the author ("Sor r", "$nd", "Constraints on K", "Force c") were checked in the
rendered PDF: all four are text-extraction artifacts; the PDF shows the correct text.
Reader-facing prose uses mathematical descriptions; development codes and identifiers appear only in the reproducibility records.

## Spanish edition
Written from the English as Spanish academic prose rather than a word-for-word translation, with the conventions of the Spanish
edition of the Latinon preprint (statement heads, lower-case references in running text, "Latinons"). A fixed glossary was used,
and the chunk translations were harmonized afterward ("coloración previa" for color-first, "especie" for the kind of a block, which
keeps "clase" for point classes). In the third round the terms were aligned with the author's definitive Spanish papers: "tabla agregada" (outline), "completación", "grafo residual", "grafo" for host, "permitido", "modalidad" for the kind of a block, "grafos escalonados", "por tanto", "paper" and "documento formal complementario". The parity check (`02_validation/PARITY.json`) passes: the same 94 display formulas, the same
3460 inline formulas in every paragraph (up to order inside a sentence), the same citations, headings, 54 numbered statements,
tables and figure, and an identical reference list. A scan found no untranslated English outside mathematics and references.

## Formal companion
English and Spanish, typeset with the series layout (monospace Consolas for Lean identifiers); 0 missing characters, 0 overfull
boxes. Every declaration reference was checked by script against the Lean sources in round 4.

## Layout
Both PDFs were compiled twice with Tectonic from the delivered TeX: 0 missing characters, 0 undefined references, one overfull box of
about 2 pt in each language (cosmetic). Every page was rendered; the title pages, Tables 1–2, Figure 1, the appendices and the
references were inspected visually in both languages. A label of the Spanish Figure 1 that crossed the vortex box was split in two
lines.

## Front matter
Preprint 1.0, 17 November 2026; DOI 10.5281/zenodo.24308221, reserved and not published (it resolves only after the deposit is
published); repository line pointing to the edition's GitHub repository. Author block as in the published papers of the series.
