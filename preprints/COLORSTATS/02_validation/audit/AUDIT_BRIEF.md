# Audit brief — color-statistics paper, release audit at the standard of paper 1 (Latinon 1.0)

You are an independent, read-only auditor. Do not edit any file and do not run Lean or Lake. You may run
small Python checks in your own scratch folder. First invoke the skill `anthropic-skills:adversarial-math-audit`.
Return your report as your final message (the harness does not let subagents write report files).

## Object
- Manuscript (semantic source, LaTeX math, numbered citations): `C:\nw\color-stats-paper\01_manuscript\color_stats_en.md`
  (PDF: `color_stats_en.pdf`, 48 pages). Citation numbers → keys: `C:\nw\color-stats-paper\editorial\citation_map.json`.
- Open content queries carried by the editorial pass: section "Content queries for the author" of
  `C:\nw\color-stats-paper\02_validation\EDITORIAL_REPORT.md` (IDs A-*, B-*, C-*, D-*, E-*, F-*). Every query in
  your scope must receive a verdict.
- Earlier audits of the research drafts (Spanish), for context only — do not trust their conclusions:
  `C:\cdr-bicolour-lean\docs\AUDITORIA_G1PP_20261116.md`, `REAUDITORIA_G1PP_20261116.md`,
  `AUDITORIA_G1PP_S58_511_20261116.md`, `REAUDITORIA_77_710_20261116.md`; ledger
  `C:\cdr-bicolour-lean\docs\PAPER_COLOUR_STATS_LEDGER_20261114.md` (§§18–25).

## Standard (as for paper 1)
A targeted written-proof review: read every statement and proof in your scope line by line, reconstruct each
step (state VERIFIED only for what you reconstructed; otherwise READ), check every constant, quantifier and
dependency, and every cross-reference. Cited theorems from other papers ([TD3] T and T+, [GJKKL], [EGJ20],
[CDR3] App. B, [LL13], Brégman, van der Waerden, Freedman, Chernoff, Hoeffding, Kim–Vu) are black boxes, but
check that their stated hypotheses are met where they are applied.

The paper passes when no finding of severity BLOCKING, SERIOUS or MINOR remains open. EDITORIAL findings
should also be reported with an exact fix. Black-box inputs are scope limitations, not findings.

## Report format (Spanish, at most 1200 words)
1. Verdict for your scope: PASS / PASS WITH RESERVATIONS / FAIL.
2. Findings, each with: ID, severity (BLOQUEANTE/SERIO/MENOR/EDITORIAL), location (section, statement,
   and a short quote), what is wrong, VERIFIED or READ, and the exact replacement text in English
   (Markdown with LaTeX math, in the style of the manuscript: plain declarative sentences, American spelling).
3. Verdict for each open content query in your scope: RESOLVED-IN-TEXT / STILL-OPEN (with the fix) /
   NOT-AN-ISSUE (with the reason).
4. What you verified exhaustively and what you only sampled.
