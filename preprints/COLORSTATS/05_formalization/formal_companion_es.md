# Documento formal complementario: conteo de sistemas triples de Steiner y cuadrados latinos con estadísticas de color prescritas

Juan Pablo Traverso Gianini

Preprint 1.0 — 17 de noviembre de 2026.

DOI: https://doi.org/10.5281/zenodo.24308221.

Repositorio: https://github.com/jtraverso/latinon-entropy-ldp.

## 1. Alcance

Este documento registra qué enunciados del manuscrito tienen contrapartida en Lean, qué demuestra
cada declaración Lean y en qué se aparta su forma del enunciado escrito. Es una guía de la fuente
entregada `ColorStats_Lean_v1.0.zip` y de sus logs, no un sustituto de las demostraciones
escritas. La numeración de los enunciados es la del manuscrito actual.

La formalización abarca las cotas superiores de los teoremas principales y el álgebra finita de las secciones 5.8–5.10:

- la cota superior (1.1) del teorema 1.1, con constante explícita;
- la proposición 1.3, con un error explícito;
- la cota de Linial–Luria por tipos de la sección 4.2 para todos los tipos de bloque, que da las
  mitades superiores de los teoremas 1.2 y 1.5, y sus análogos para 1-factorizaciones (mitad
  superior del teorema 1.7) y para grafos escalonados típicos (mitad superior del teorema 1.9(a));
- los lemas 5.12, 5.13, 5.14, 5.16, 5.17, 5.18, 5.19 y 5.20;
- tres implicaciones condicionales entre resultados principales (sección 6 de este documento).

No abarca las cotas inferiores. En particular, **no** están formalizados: la mitad inferior (1.2)
del teorema 1.1; las cotas inferiores de los teoremas 1.2, 1.5, 1.7 y 1.9(a); el teorema 1.9(b);
el teorema 1.10; los corolarios 1.4, 1.6 y 1.8; el corolario 1.11, salvo como consecuencia del
teorema 1.10. Tampoco se formaliza aquí nada de la maquinaria de las secciones 5.1–5.7 y 6
(coloración aleatoria, el teorema de emparejamientos de Glock, Joos, Kim, Kühn y Lichev,
limpieza, cobertura descendente, completación con T y T⁺, intercambios, contabilidad), ni los
lemas 2.1 (salvo como paso interno; véase la sección 3), 3.1, 4.1, 4.2, 5.1–5.11, 5.8′, 5.21,
las observaciones 4.3, 5.15, 5.22 o los lemas de la sección 6. Para esos resultados, la
formalización contiene a lo sumo un enunciado Lean (sección 7).

Cada declaración demostrada que se enumera en la sección 3 se comprobó con `#print axioms`; todos
los conjuntos de axiomas informados están contenidos en `propext`, `Classical.choice` y
`Quot.sound` (sección 8). Esto indica que las declaraciones enumeradas están demostradas en Lean a
partir de esos axiomas; no dice nada sobre los resultados que solo están enunciados.

## 2. Convenciones y notación

**Nombres.** Los identificadores Lean conservan la grafía británica del proyecto (`ColourStats`,
`colour_first_Phi`, `colour_load`), mientras que el paper escribe «color». En Lean, `Phi`
designa tanto la tasa como las inversas por la derecha:

| Paper | Lean |
|---|---|
| tasa `Φ(t)` (todos los tipos) | `ColourStats.Phi lab t` (`Challenge.lean`) |
| tasa `Φ(t)` (bicoloreada, proposición 1.3) | `ColourStats.Prop13.Phi c t` |
| tasa del teorema 1.7 | `ColourStats.Statements.Phi1F lab col t` |
| tasa `Φ_G(t)` | `ColourStats.Statements.PhiG G lab t` |
| inversa por la derecha `Ψ` del lema 5.13 | el valor por triángulo `y x u v + y x u w + y x v w` (`TriangleInverse.y`) |
| inversa por la derecha `Ψ` del lema 5.16 | `ColourStats.E2Inverse.Phi xV xC` |
| `Ψ₁`, `𝒯` del lema 5.19 | `E3Gadget.Phi₁`, `E3Gadget.Tmap`; sobre el grafo, `Host519.Phiop`, `Host519.Top` |
| `Ψ̃`, `Ψ` del lema 5.19 | el operador construido en `E3Assembly.right_inverse_of_estimates`; la `Φ` cuya existencia afirma `lemma_5_19_exists` |
| `N_τ`, `e_π`, `c_X`, `m_π(τ)` | `numTriples`, `numPairs`, `classSize`, `mult` |
| `N^all_t`, `N^{1F}_t`, `#dec_t(G)`, `#LS(M)` | `countAll`, `count1F`, `countDecomp`, `numLS` |

**Logaritmo de cero.** Lean fija `log 0 = 0`. Un enunciado `log N ≤ Φ + εn²` con `N = 0` afirma
entonces `Φ + εn² ≥ 0`, algo que el paper no sostiene. Por eso cada cota superior se demuestra
de dos formas: una forma exponencial `N ≤ exp(Φ + εn²)`, que es la fiel, y la forma logarítmica
del enunciado del paper, demostrada para todo `N ≥ 0` probando por separado que el lado derecho
es no negativo bajo las hipótesis.

**Enunciados asintóticos.** `o(n²)` se expresa así: para todo `ε > 0` existe `n₀` tal que, para
todo `n ≥ n₀`, toda partición y todo vector de tipos que cumplan las hipótesis, la cota vale con
`εn²`. Como `n₀` se elige antes que la partición y que `t`, las cotas son uniformes, como en el
paper.

**Numeración de borrador en las fuentes.** `README.md`, los docstrings de `Challenge.lean` y
`Statements.lean`, y `docs/ROADMAP_ES.md` remiten al borrador 6 (14 de noviembre de 2026) y a su
título anterior. La numeración de enunciados que usan allí coincide con la del manuscrito actual.
Las fuentes se congelaron sin modificaciones.

## 3. Correspondencia de enunciados

Todos los módulos están bajo `lean/ColourStats/`; los números de línea remiten a la fuente
congelada.

### 3.1 Resultados principales (cotas superiores)

| Paper | Declaración Lean (módulo:línea) | Qué se demuestra; diferencia de forma |
|---|---|---|
| Teorema 1.1, cota superior (1.1) | `ColourStats.LatinUpper.theorem_1_1_upper` (`LatinUpper.lean:569`), que demuestra `LatinUpper.Theorem_1_1_upper` | Para `a, b, c` y `δ₀, ζ > 0` fijos: `log #LS(M) ≤ n²(log n − 2 − TC(Q)) + K n log² n` con `K = 8c`, `n ≥ max(3, ⌈e^{2+a+b}⌉)`, para toda partición con clases `≥ δ₀n` y toda tabla agregada con `M/n² ≥ ζ`. Coincide con (1.1) y con la primera componente de la conjunción `Statements.Theorem_1_1`; vale también cuando `#LS(M) = 0` (se demuestra que el lado derecho es no negativo). |
| Proposición 1.3 | `ColourStats.prop_1_3_bicol` (`Prop13Bridge.lean:130`); `ColourStats.Prop13.prop_1_3` (`Prop13.lean:147`); identidad exacta `Prop13.prop_1_3_exact` (`Prop13.lean:100`); `ColourStats.Phi_bicolTypes` (`Prop13Bridge.lean:84`) | `|Φ(t) − (n²/6)(log n − 2 − D(Q‖P₀))| ≤ (n/6)|log n − 2| + n`, suponiendo `c_X ≥ 2`, `t_XY > 0`, las identidades de fila de (1.3) y `3Σ c_X(c_X−1) = n(n−1)`. Error explícito en lugar de `O(n log n)`, con hipótesis más débiles. |
| (4.3) y (5.2): cota de Linial–Luria por tipos | `ColourStats.TypedSTS.typed_upper` (`TypedFinal.lean:137`) | Si `N^all_t > 0` y cada clase tiene `≥ c₁ + 2` puntos (`c₁ ≥ 1`): `log N^all_t ≤ Φ(t) + n²((5 log n + 16)/n + 8 c₁^{−1/4})`, para todo vector de tipos `t` y todos los tipos de bloque. Forma `Φ(t)`, no la forma normalizada con `D(Q‖P)`; error `O(n^{7/4})` (sección 4). |
| Teorema 1.5, mitad superior (y teorema 1.2, mitad superior) | `ColourStats.TypedSTS.theorem_1_5_upper_exp` (`TypedThm.lean:90`); `ColourStats.UpperLog.theorem_1_5_upper` (`UpperLog.lean:104`), que demuestra `Challenge.Theorem_1_5_upper`; `TypedSTS.upper_log` (`TypedThm.lean:123`) | Forma exponencial `N^all_t ≤ exp(Φ(t) + εn²)` para todo `t` (sin identidades de pares ni congruencia sobre `n`), con `n₀` explícito; forma logarítmica exactamente como en `Theorem_1_5_upper`, incluido `N = 0`. Teorema 1.2: instancia `t := bicolTypes t` (sin declaración propia). |
| Teorema 1.7, mitad superior; (5.3) | `ColourStats.Typed1F.typed_upper_1F` (`Typed1FMain.lean:160`); `Typed1F.theorem_1_7_upper_exp` (`Typed1FMain.lean:315`); `ColourStats.UpperLog.theorem_1_7_upper` (`UpperLog.lean:135`), que demuestra `Statements.Theorem_1_7_upper` | `log N^{1F}_t ≤ Φ(t) + n²((log n + 4)/n + 7 h₁^{−1/4})` cuando cada clase de color tiene `≥ h₁ + 1` colores; forma exponencial para todo `t` (solo se necesitan clases de color `≥ δ₀n`); forma logarítmica tal como está enunciada. |
| Teorema 1.9(a), mitad superior; (5.4) | `ColourStats.TypedG.typed_upper_G` (`TypedGFinal.lean:140`); `TypedG.theorem_1_9a_upper_exp` (`TypedGThm.lean:47`); `ColourStats.TypedG.theorem_1_9a_upper` (`UpperLog.lean:193`), que demuestra `Statements.Theorem_1_9a_upper` | Para `G` `(η, 5)`-típico con `η ≤ 1/3` y en el que cada arista tiene `≥ c₁` vecinos comunes en cada clase: `log #dec_t(G) ≤ Φ_G(t) + n²((5 log n + 16)/n + 8 c₁^{−1/4} + η)`; forma exponencial bajo `TypHyp` (las hipótesis del teorema 1.9) para todo `t`; forma logarítmica tal como está enunciada. No se usan las identidades de pares (1.6) ni la triángulo-divisibilidad. |
| No negatividad de las tasas (para `log 0`) | `UpperLog.Phi_nonneg` (`UpperLog.lean:69`), `UpperLog.Phi1F_nonneg` (`UpperLog.lean:120`), `TypedG.PhiG_nonneg` (`UpperLog.lean:159`), `LatinUpper.TC_le` (`LatinUpper.lean:133`) | `Φ ≥ 0` bajo las identidades y con clases de tamaño `≥ 26` (resp. clases de color `≥ 8`, `≥ 24` vecinos comunes); `TC(Q) ≤ a + b`. No son enunciados del paper. |

Declaraciones auxiliares de la sección 4.1: `Bregman.bregman` (`Bregman.lean:191`, el teorema de
Bregman `log #PM(A) ≤ Σ_i log(|A_i|!)/|A_i|`, demostrado mediante el argumento de entropía de
Radhakrishnan), `Bregman.sum_rank` (`Bregman.lean:107`), `LatinUpper.bregman_sum_le` (`:75`),
`LatinUpper.log_card_Patt_le` (`:232`, el conteo de patrones), `LatinUpper.log_LSset_le` (`:368`,
la cota por regla de la cadena), `LatinUpper.TC_identity` (`:162`). Las identidades de márgenes del
lema 2.1 para cuadrados latinos concretos se demuestran internamente (`LatinUpper.margin_rc`,
`LatinUpper.margin_s`, líneas 497 y 518).

Declaraciones auxiliares de la sección 4.2: `TypedChain.chain_typed` (`TypedChain2.lean:160`, la
regla de la cadena en forma de conteo, con la clase del tercer punto revelada por separado),
`TypedChain.cond_le` (`TypedChain.lean:255`, condicionar reduce la entropía),
`TypedSTS.good_of_mem` (`TypedSTS.lean:293`, los seis pares del paso 5), `TypedSTS.point_sum_le`
(`TypedBox.lean:235`), `TypedSTS.pair_bound` (`TypedPair.lean:212`), `TypedSTS.typed_raw_bound`
(`TypedAssembly.lean:53`), `TypedSTS.typed_agg_bound` (`TypedAggregate.lean:198`, paso 4),
`TypedSTS.term_le` (`TypedAnalytic.lean:89`, pasos 5–6), `TypedSTS.Mstat_eq`
(`TypedStats.lean:69`); para 1-factorizaciones, `Typed1F.good_of_mem` (`Typed1F.lean:120`),
`Typed1F.raw_bound` (`Typed1FAgg.lean:174`); para grafos escalonados típicos, `TypedG.good_of_memG`
(`TypedG.lean:208`), `TypedG.typed_agg_boundG` (`TypedGAgg.lean:207`), `TypedG.MstatG_eq`
(`TypedGStats.lean:146`), `TypedG.sum_cnb` (`TypedGStats.lean:268`). El orden aleatorio
`λ_e ∈ [0, 1]` del paper se sustituye por etiquetas en `Fin L` promediadas uniformemente; las
integrales de los pasos 5–6 se convierten en sumas finitas, y de ahí provienen los términos
`log n / n` y `c₁^{−1/4}` del error.

### 3.2 Lemas de la sección 5

| Paper | Declaración Lean (módulo:línea) | Qué se demuestra; diferencia de forma |
|---|---|---|
| Lema 5.12 | `ColourFirst.compl_mul_typeNum` (`ColourFirst.lean:99`); `ColourFirst.apex_eq` (`:130`), `ColourFirst.apex_indep` (`:157`); `ColourFirst.sum_P` (`:168`); `ColourFirst.entropy_identity` (`:189`), `ColourFirst.entropy_identity_one` (`:274`); `ColourStats.card_type` (`TypeCount.lean:53`), `ColourStats.numTriples_eq` (`:96`), `ColourStats.colour_first_Phi` (`:109`) | El doble conteo `w(τ,π)e_π = m_π(τ)N^O_τ`; (a) `D_τ` no depende del ápice (clases de tamaño `≥ 2`, `ν > 0`); (b) la identidad de entropía para `ν, t'` positivos (clases de tamaño `≥ 3`), sin las identidades de pares, que solo sirven para que `P(·|π)` sea una probabilidad (`sum_P`); con `ν ≡ 1`, `t' = t`, el lado derecho es `Φ(t)`. |
| Lema 5.13 | `TriangleInverse.apply_inverse` (`TriangleInverse.lean:78`), `TriangleInverse.inverse_bound` (`:95`) | `AΨx = x` para `x` simétrico con diagonal nula y `m ≥ 5` (paper: `m ≥ 6`); `‖Ψx‖_∞ ≤ 24‖x‖_∞/m` para `m ≥ 8`. Las mismas fórmulas `S`, `Y`, `y`. |
| Lema 5.14 | `ColourStats.hub_pairPreserving` (`PaschHub.lean:237`), `ColourStats.hub_unique` (`:115`), `ColourStats.hub_basis` (`:266`); `ColourStats.finrank_Lam` (`PaschRank.lean:187`), `ColourStats.card_avoid` (`:84`), `ColourStats.hub_eq_pasch` (`:253`), `ColourStats.pasch_same_pairs` (`:211`) | Los vectores pivote están en `Λ`; todo `d ∈ Λ` es igual a `Σ_{σ ∌ o} d_σ b_σ`, y un `d` que se anula fuera de los tipos que contienen `o` es nulo; `rank Λ = C(k+1, 3)`; `b_σ` es el cambio de tipos de el intercambio de Pasch de `{013, 024, 125, 345}` a `{012, 034, 135, 245}`, y ambas familias cubren los mismos doce pares. Como en el paper. |
| Lema 5.16 | `E2Inverse.pair_load` (`E2Inverse.lean:101`), `E2Inverse.colour_load` (`:134`), `E2Inverse.inverse_bound` (`:154`) | `AΨx = x` para `x` balanceado (las cargas de pares usan el balance; las cargas de colores solo necesitan diagonal nula); `|Ψx| ≤ 13(1 + m/h)‖x‖/min(m, h)` para `m ≥ 3`, `h ≥ 1`. La constante «`K` absoluta» del paper es `K = 13`; el valor 9 que da la demostración escrita para `m ≥ 4` no está formalizado. |
| Lema 5.17 | `E2Lattice.mem_span_of_rich` (`E2Lattice.lean:206`); forma dual `E2Lattice.sum_eq_zero_of_rich` (`:58`) | Para `H ⊂ K_m ∨ C_h` dado por un grafo `G` sobre los vértices y un conjunto `EC` de pares vértice–color, que satisface `Rich` (tres colores tienen un vecino común que es un vértice; dos vértices, no necesariamente distintos, adyacentes a los colores `c, c'` tienen un vecino común que es un vértice y es adyacente a `c, c'`; toda arista entre vértices está en un triángulo con un color), balanceado en cada vértice y con grados de color pares: `1_{E(H)}` está en el ℤ-span de los triángulos `{u, v, c}` de `H`. Las hipótesis de riqueza son exactamente las del lema 5.17 actual. La conclusión de Lean es una combinación entera de triángulos, como en el paper. |
| Lema 5.18 | `E2Swap.swapVec_inLambda` (`E2Swap.lean:81`), `E2Swap.inLambda_unique` (`:111`), `E2Swap.inLambda_repr` (`:187`), `E2Swap.finrank_Lam2` (`E2SwapRank.lean:170`) | Los vectores de trueque están en `Λ`; los `C(k,2)(ℓ−1)` trueques sobre las clases `(o, o, Y, Z)` entre `ω` y `Γ` forman una base cuyos coeficientes son las coordenadas libres `d(π, Γ)`, `π ∌ o`; `rank Λ = C(k,2)(ℓ−1)`. Es la base explícita que sigue a la demostración del lema 5.18. El cambio de tipos de un trueque se define al nivel de los vectores de tipos, no se deduce de una 1-factorización concreta; la primera demostración (vía `L_even`) y los conteos «cuatro por cuatro» y «ocho unidades con signo» no están formalizados. |
| Lema 5.19 | `Host519.lemma_5_19_exists` (`Lemma519.lean:202`); versión explícita `Host519.Hyp.lemma_5_19` (`Lemma519.lean:182`) | Para todo `δ₀ ∈ (0, 1]`, `d₀ > 0` existen `η₀ > 0`, `m₀`, `K` tales que todo grafo `(η, 5)`-típico con `0 ≤ η ≤ η₀`, `m ≥ m₀` vértices, clases `≥ δ₀m` y densidades en `[d₀, 1]` tiene una inversa por la derecha lineal y continua `Φ` (paper: `Ψ`) de `A` con `‖Φ‖_{∞→∞} ≤ K/m`. Las constantes dependen solo de `δ₀, d₀` (paper: también de `k`). La versión explícita da `‖Φ‖ ≤ 2(108/p + 108/p² + 4/(δ₀³d₀³))/m` con `p = pconst δ₀ d₀`, bajo `eps1 + 4η/(δ₀²d₀) ≤ 1/2`. |
| Lema 5.19, piezas | `E3Gadget.gadget_identity` (`E3Gadget.lean:56`), `E3Gadget.apply_Phi₁` (`:78`), `Host519.mulVec_gadget` (`Host519.lean:115`), `Host519.A_comp_Phi₁` (`:178`), `Host519.Hyp.norm_Phiop_le` (`Phi519.lean:142`), `Host519.Hyp.abs_K2_sub_disjoint` (`K2519.lean:139`), `Host519.Hyp.norm_E₁_le` (`Lemma519.lean:95`), `PairMap.pairMap_surjective` (`PairMap.lean:83`), `Weighting.idealLoad_weight` (`Weighting.lean:73`), `Weighting.load_weight_error` (`WeightingError.lean:46`), `Typical.load_estimate` (`Typical.lean:81`), `Counting.card_edgesIn_commonIn` (`Counting.lean:162`), `Neumann.exists_right_inverse` (`Neumann.lean:31`), `E3Assembly.right_inverse_of_estimates` (`E3Assembly.lean:39`), `E3Assembly.opNorm_le_of_rowSum` (`:90`) | La identidad del dispositivo `K₄`, `Ag(e,f) = 1_e − 1_f`; `AΨ₁ = I − 𝒯`; `‖Ψ₁‖ ≤ 108/(pm)`; el núcleo de dos pasos `Π₂` está a menos de `19η/M` del uniforme sobre pares disjuntos; `‖𝒯² − σ ⊗ u‖ ≤ eps1`; la aplicación de pares es sobreyectiva; la ponderación `W` y su error de carga; el paso de Neumann; el ensamblaje a partir de las cuatro estimaciones. Siguen los pasos de la demostración escrita. |
| Lema 5.20 | `E3Lattice.isPhysical_of_rich` (`E3Lattice.lean:204`); forma dual `E3Lattice.sum_eq_zero_of_rich` (`:65`) | Si `G` es `Rich` (cada dos aristas tienen un `⊠`-compañero común; cada tres vértices, no necesariamente distintos, tienen un vecino común; dos vecinos comunes de dos vértices distintos están unidos por un camino dentro de su vecindario común), todos los grados son pares y `3 ∣ e(G)`, entonces `1_{E(G)}` está en el retículo de triángulos del corpus (`TypedTriangle.IsPhysical`, con todos los triángulos permitidos). Las mismas hipótesis y la misma conclusión (una combinación entera de triángulos) que el paper. |

## 4. Diferencias entre los resultados en Lean y los enunciados escritos

1. **Error de las cotas superiores.** Las cotas en Lean tienen error
   `n²((5 log n + 16)/n + 8 c₁^{−1/4})` con `c₁ ≈ δ₀n`, es decir, `O(n^{7/4})` (y
   `n²((log n + 4)/n + 7 h₁^{−1/4})` para 1-factorizaciones). El manuscrito demuestra por escrito
   `O(n^{3/2})` (§4.2, paso 5; §5.11, usado en el teorema 1.10). La formalización establece los
   enunciados `o(n²)` de los teoremas 1.2, 1.5, 1.7 y 1.9(a) (mitades superiores) con este error
   explícito `O(n^{7/4})` (más `ηn²` en el teorema 1.9(a)), no con el error `O(n^{3/2})`. De las cotas explícitas puede leerse un
   error `O(n^{2−c})` con `c = 1/4` (`c = min(1/4, c₀)` para el teorema 1.9), pero ninguna
   declaración Lean enuncia la forma polinomial.
2. **Lema 5.17.** El enunciado actual del lema 5.17 enumera las condiciones de riqueza bajo las
   cuales Lean demuestra el lema, y coinciden con `E2Lattice.Rich` de Lean. La discrepancia
   anterior (una hipótesis que, leída literalmente, forzaba `H = K_m ∨ C_h`) ya no existe. Las
   conclusiones de los lemas 5.17 y 5.20 (combinaciones enteras de triángulos) también coinciden
   con Lean; no queda ninguna diferencia.
3. **`log 0 = 0`.** Los enunciados logarítmicos de Lean son más fuertes que el paper cuando el
   conteo es cero (sección 2). El contenido adicional está demostrado. Las formas exponenciales
   recogen exactamente el contenido del paper.
4. **Formas exponencial y logarítmica.** `theorem_1_5_upper_exp`, `theorem_1_7_upper_exp` y
   `theorem_1_9a_upper_exp` enuncian `N ≤ exp(Φ + εn²)` para todo vector de tipos; `upper_log` y
   los tres teoremas de `UpperLog` dan `log N ≤ Φ + εn²`, los tres últimos para todo `N ≥ 0`.
5. **Proposición 1.3.** Lean da el error explícito `(n/6)|log n − 2| + n` y solo necesita las
   identidades de fila de (1.3) y la identidad de admisibilidad, no todas las hipótesis del
   teorema 1.2.
6. **Formas normalizadas.** Las cotas superiores se demuestran en la forma `Φ(t)`. La forma
   normalizada `(n²/6)(log n − 2 − D(Q‖P))` del teorema 1.5 y de (5.2), y la forma
   `C(n,2)(log n − 2 − D(Q‖P))` del teorema 1.7 y de (5.3), no están formalizadas; la
   normalización solo se formaliza para la tasa bicoloreada (proposición 1.3).
7. **Teorema 1.1.** La cota superior (1.1) se demuestra tal como está enunciada, con `K = 8c`,
   pero por una vía distinta de la de los lemas 4.1–4.2: un único argumento de regla de la cadena,
   primero sobre el patrón de clases y luego sobre los símbolos, con el teorema de Bregman
   demostrado dentro del proyecto. Los lemas 4.1 y 4.2 y la observación 4.3 no están formalizados
   como enunciados.
8. **Diferencias menores de hipótesis** (lema 5.12, clases de tamaño `≥ 3`; lema 5.13, `m ≥ 5`;
   lema 5.16, `K = 13`; lema 5.19, constantes independientes de `k`; lema 5.18, al nivel de los
   vectores de tipos): se detallan en la sección 3 y en `MAPPING_NOTES.md`.

## 5. El teorema 1.2 y el conteo bicoloreado

`countAll lab (bicolTypes t)` cuenta los sistemas triples de Steiner con exactamente `t_XY` bloques
de tipo `XXY` para `X ≠ Y` y ningún bloque de otro tipo, es decir, los sistemas bicoloreados con
matriz de tipos `t`. La mitad superior del teorema 1.2 es la instancia `t := bicolTypes t` de
`theorem_1_5_upper_exp`, y `Phi_bicolTypes` identifica `Φ(bicolTypes t)` con la tasa bicoloreada
de la proposición 1.3. No hay una declaración propia para la mitad superior del teorema 1.2.

## 6. Implicaciones condicionales

| Implicación | Declaración Lean (módulo:línea) | Contenido |
|---|---|---|
| Corolario 1.11 ⇐ teorema 1.10 para el teorema 1.9(a) | `ColourStats.Statements.corollary_1_11_of` (`Cor111.lean:266`), con `Statements.completionEquiv` (`Cor111.lean:103`) y `Statements.triDivisible_leave` (`Cor111.lean:237`) | `Theorem_1_10_typical → Corollary_1_11`. Las completaciones de un sistema parcial `Q` con vector de tipos `t` están en biyección con las descomposiciones en triángulos de `K_n − L_Q` con vector de tipos `t − t(Q)`, y `K_n − L_Q` es triángulo-divisible para `n ≡ 1, 3 (mod 6)`. |
| Teorema 1.5 ⇐ teorema 1.9(a) | `ColourStats.Statements.theorem_1_5_of` (`Thm15From19.lean:113`) | `Theorem_1_9a → Theorem_1_5`, aplicando el teorema 1.9(a) a `G = K_n`. |
| Teorema 1.1 ⇐ su mitad inferior | `ColourStats.LatinUpper.theorem_1_1_of_lower` (`LatinUpper.lean:704`) | La cota inferior (1.2), tomada como hipótesis, junto con `theorem_1_1_upper` da `Statements.Theorem_1_1`. |

Las hipótesis de estas implicaciones no están demostradas en Lean.

## 7. Solo enunciados

Dos archivos contienen enunciados Lean (como definiciones de tipo `Prop`) sin demostración:

- `Challenge.lean`: `Theorem_1_2`, `Theorem_1_5`, `Theorem_1_5_upper` (este último se demuestra en
  `UpperLog.lean`).
- `Statements.lean`: `Theorem_1_1` (la componente superior está demostrada; el enunciado completo
  solo se demuestra a partir de la mitad inferior), `Corollary_1_4`, `Corollary_1_6`,
  `Theorem_1_7`, `Theorem_1_7_upper` (demostrado), `Corollary_1_8`, `Theorem_1_9a`,
  `Theorem_1_9a_upper` (demostrado), `Theorem_1_9b`, `Theorem_1_10` (con las partes
  `Theorem_1_10_latin`, `_bicol`, `_all`, `_oneFact`, `_typical`) y `Corollary_1_11`.

Estos enunciados fijan la lectura elegida para cada resultado: la mitad inferior del teorema 1.1
supone las identidades de márgenes (`OutlineMargins`), como en el manuscrito actual; los principios
de grandes desviaciones se enuncian mediante conteos (`CountLDP`), lo que, para una tasa continua
sobre un conjunto factible compacto, equivale al par de cotas estándar. Dos de ellos difieren del
manuscrito actual:

- `Theorem_1_10` abarca la mitad inferior del teorema 1.1 y los teoremas 1.2, 1.5, 1.7 y 1.9(a),
  pero no el teorema 1.9(b) ni el enunciado sobre bolas de los corolarios 1.6 y 1.8. Su docstring
  dice que el enunciado de los corolarios no especifica los entornos; el manuscrito actual sí los
  especifica (bolas cerradas con centro en `F_n`), de modo que ese comentario está desactualizado.
- `Theorem_1_5` y `Theorem_1_7` enuncian solo la igualdad con `Φ(t)`, no la forma normalizada.

## 8. Resultados de compilación y de axiomas

Toolchain `leanprover/lean4:v4.35.0-rc3`; Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`;
corpus `cdr_prescribed_bicolorings` 0.3.0, idéntico byte a byte en sus fuentes a
`CDRIII_Lean_v1.0.zip` (detalles en `lean/DEPENDENCIES.md`). La biblioteca `ColourStats` tiene 57
módulos (la raíz `ColourStats.lean` y 56 módulos bajo `ColourStats/`), con 63 archivos fuente en
el archivo comprimido.

**Compilación en el directorio del proyecto (17 de noviembre de 2026).**
`lake build --no-build ColourStats` informó que todos los objetivos estaban al día (9030 jobs), de
modo que no hacía falta recompilar nada de lo anterior. Después, `lake build ColourStats` terminó
con código de salida 0, "Build completed successfully (9030 jobs)", en 25 segundos. Esta ejecución
reutilizó los resultados de compilación existentes, cuyas trazas coinciden con las fuentes
actuales; no recompiló ningún módulo. Log: `logs/build_ColourStats.log`.

**Compilación desde el archivo comprimido (17 de noviembre de 2026).** Para comprobar que el
archivo está completo y compila desde las fuentes, `ColorStats_Lean_v1.0.zip` se extrajo en un
directorio nuevo, situado de modo que la ruta relativa al corpus se resolviera. Allí,
`lake build --no-build ColourStats` solo listó como desactualizados módulos `ColourStats.*`. Un
primer `lake build ColourStats` con el paralelismo por defecto de Lake se quedó sin memoria
(`std::bad_alloc` en once procesos Lean simultáneos; log
`logs/rebuild_from_archive_attempt1_oom.log`). La segunda ejecución, con `LEAN_NUM_THREADS=1`,
compiló desde las fuentes los 57 módulos de `ColourStats`, reutilizó el corpus y Mathlib, y terminó
con "Build completed successfully (9030 jobs)", código de salida 0, en 2362 segundos. Log:
`logs/rebuild_from_archive.log`. El directorio temporal se eliminó después.

**Axiomas.** `lake env lean checks/Axioms.lean` ejecutó 89 consultas `#print axioms` (455
segundos, código de salida 0). Cada consulta informa exactamente
`[propext, Classical.choice, Quot.sound]`; ninguna consulta informa `sorryAx` y ningún archivo
fuente contiene `sorry`, `admit` ni un `axiom` de usuario. Log: `logs/axioms.log`. Las mismas 89 consultas, ejecutadas sobre los
módulos compilados desde el archivo comprimido, dieron el mismo resultado (código de salida 0, 74
segundos; `logs/axioms_from_archive.log`).

**Archivo comprimido.** `ColorStats_Lean_v1.0.zip`, SHA-256
`5091a807b3929336f74ea3cfb2d0f62a43c09ce44194c02cf9b78b71d907cd47`, 205061 bytes, 65 archivos
bajo `lean/` (63 archivos fuente, `DEPENDENCIES.md`, `source_manifest.json`).

Las 89 consultas cubren todas las declaraciones nombradas en las secciones 3 y 6, salvo los lemas
internos `LatinUpper.margin_rc`, `LatinUpper.margin_s`, `UpperLog.Phi1F_nonneg` y
`LatinUpper.TC_le`, que se usan en las demostraciones de teoremas consultados
(`theorem_1_1_upper`, `theorem_1_7_upper`) y quedan cubiertos por esas consultas.

## 9. Reconstrucción

1. Extraiga `ColorStats_Lean_v1.0.zip`; el proyecto es la carpeta `lean/`. Compruebe los archivos
   con `lean/source_manifest.json`.
2. Instale `leanprover/lean4:v4.35.0-rc3`.
3. Obtenga el corpus (la fuente Lean de `CDRIII_Lean_v1.0.zip`, DOI 10.5281/zenodo.24201563) y su
   Mathlib en la revisión fijada. Coloque el corpus en `../cdr-clean-20261113/snapshot/lean`
   respecto del proyecto, o bien modifique `path` y `packagesDir` del corpus en `lakefile.toml`.
   Ni el corpus ni Mathlib se incluyen en el paquete.
4. Desde `lean/`, ejecute secuencialmente:

       lake build --no-build ColourStats   # only ColourStats.* should be out of date
       lake build ColourStats
       lake env lean checks/Axioms.lean

   En una máquina con poca memoria, fije `LEAN_NUM_THREADS=1` para la compilación, de modo que
   Lake compile un módulo cada vez.

## 10. Procedencia

El directorio del proyecto `C:\nw\colour-stats-lean` no está bajo control de versiones. El archivo
comprimido se generó a partir de él el 17 de noviembre de 2026 sin modificar ningún archivo.
`FREEZE.json` vincula el archivo comprimido, los hashes de sus entradas y los logs. La instantánea
del corpus se obtuvo de la reconstrucción limpia de CDR III a partir del commit de fuentes
`8756b2ef2dbe56002617a86e97e1b16a790ae069`; de sus 1307 módulos, 13 están en la clausura de imports
de `ColourStats` (`lean/DEPENDENCIES.md`).
