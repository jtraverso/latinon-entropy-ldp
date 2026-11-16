# Documento formal complementario: entropía y grandes desviaciones para cuadrados latinos

Juan Pablo Traverso Gianini

Preprint 1.0 — 16 de noviembre de 2026.

Repositorio: https://github.com/jtraverso/latinon-entropy-ldp.

## 1. Alcance e interfaz matemática

Este documento registra cómo se representan en Lean los enunciados del manuscrito. Es una guía de las fuentes y evidencias entregadas, no un reemplazo de las demostraciones escritas. El modelo tiene tres márgenes uniformes de dos coordenadas y conserva el mapa de orden que preserva la medida. Su distancia tiene dos términos de orden y un término de distribución que prueba intervalos de símbolos. La entropía relativa toma valores en los reales no negativos extendidos. Su conversión a un número real solo se justifica después de una hipótesis de tasa finita.

Los enunciados formales son los contratos protegidos del registro de auditoría. El resultado superior usa `ENNReal.ofReal t`; este es el piso no estricto max(t,0) del manuscrito. El resultado inferior requiere un costo testigo finito no negativo. Ninguno presupone una ley sobre una colección auxiliar: ambos se refieren al transporte de la ley uniforme finita real de cuadrados latinos.

## 2. Correspondencia de enunciados principales

**Theorem 2.1 / Teorema 2.1**

`LatinonEntropy.closed_uniform_latinon_upper`

Fuente: `lean/LatinonBridge/LatinonGlobalDeviations.lean`, línea 20.

`LatinonEntropy.open_uniform_latinon_lower`

Fuente: `lean/LatinonBridge/LatinonGlobalDeviations.lean`, línea 46.

**Theorem 2.2 / Teorema 2.2**

`LatinonEntropy.finite_rate_standard_pattern_log_count`

Fuente: `lean/LatinonPatternConjecture.lean`, línea 12.

`LatinonEntropy.empty_standard_pattern_fiber_eventually_zero`

Fuente: `lean/LatinonPatternConjecture.lean`, línea 42.

**Theorem 3.1 / Teorema 3.1**

`LatinonEntropy.finite_latin_tensor_lower_bound`

Fuente: `lean/LatinTensorLowerBound.lean`, línea 51.

**Lemma 4.1 / Lema 4.1**

`LatinonEntropy.correction_lemma`

Fuente: `lean/QuasirandomCorrection.lean`, línea 143.

La proposición 2.3 es la identificación escrita con las representaciones y la definición de distancia de corte publicadas por GHHS. Su prueba mediante desintegración y cambio de variables está en el manuscrito; no se presenta como una declaración Lean nueva. La fuente formal usa la representación por medidas, transportes inversos de coordenadas y dos términos de orden. La notación del manuscrito no renombra ninguna declaración Lean.

**Tasa buena en el teorema 2.1**

`LatinonEntropy.latinon_rate_lowerSemicontinuous`

Fuente: `lean/LatinonFullDyadicKL.lean`, línea 42.

`LatinonEntropy.latinon_full_cut_compact`

Fuente: `lean/LatinonBridge/LatinonCompactness.lean`, línea 60.

`LatinonEntropy.latinon_rate_sublevels_compact`

Fuente: `lean/LatinonBridge/LatinonGlobalDeviations.lean`, línea 15.

Estas tres propiedades tienen sus propias consultas de axiomas en los módulos de fuentes. El informe de reconstrucción completada registra sus tres salidas exitosas por separado de las ocho consultas seleccionadas de resultados finales en `ReviewAxioms.lean`. Las once informaron solo los axiomas fundacionales estándar. Véase `preprints/LATINON/02_validation/CLEAN_REBUILD_AUDIT.json`.

El teorema finito de tensores cuantifica el umbral de orden antes del perfil. El teorema de corrección no tiene hipótesis de diámetro residual ni certificados de potenciales. El lema 4.1 conserva sus constantes explícitas de caja y el coeficiente lineal 3.

El argumento de diámetro seis también aparece internamente como `LatinonEntropy.ScaledResidualData.diameter_six` en `lean/ResidualDiameter.lean`. Su ausencia de las hipótesis de `correction_lemma` significa que se deduce internamente, no que solo exista en papel. Se revisa el lema 4.1 como prueba escrita por separado de su correspondencia con ese argumento de fuentes.

## 3. Registro de dependencias

El registro central tiene 23 pasos. La lista siguiente da la declaración y las dependencias en cada paso. La correspondencia actual con las fuentes compiladas está en `publication/PROOF_LEDGER.json`. Los certificados originales ligados a fuentes que se conservan dentro del archivo Lean son evidencia histórica; el informe de reconstrucción completada certifica la selección entregada.

**1. Modelo y distancia completa.**

`LatinonEntropy.LatinonMeasure`

Dependencias en el registro: ninguna.

**2. Corrección determinista.**

`LatinonEntropy.correction_lemma`

Dependencias en el registro: ninguna.

**3. Permanentes y marginales.**

`LatinonEntropy.permanental_marginal_l1_le`

Dependencias en el registro: ninguna.

**4. Proceso latino y parada.**

`LatinonEntropy.profileProcessPolicy`

Dependencias en el registro: 2, 3.

**5. Recurrencia del defecto.**

`LatinonEntropy.profile_expected_defect_recurrence`

Dependencias en el registro: 4.

**6. Estabilidad por Gronwall.**

`LatinonEntropy.profile_expected_defect_uniform`

Dependencias en el registro: 5.

**7. Supervivencia uniforme.**

`LatinonEntropy.eventually_uniform_profile_survival`

Dependencias en el registro: 6.

**8. Cercanía uniforme en cortes.**

`LatinonEntropy.eventually_uniform_profile_closeness`

Dependencias en el registro: 7.

**9. Entropía del proceso completo.**

`LatinonEntropy.profile_history_entropy_lower`

Dependencias en el registro: 6, 7.

**10. Conteo inferior de tensores.**

`LatinonEntropy.finite_latin_tensor_lower_bound`

Dependencias en el registro: 8, 9.

**11. Puente tensor-Latinon.**

`LatinonEntropy.finite_latin_grid_metric_ball_lower_bound`

Dependencias en el registro: 1, 10.

**12. Cota superior de particiones.**

`LatinonEntropy.exists_latinon_partition_ball_count_upper`

Dependencias en el registro: 1.

**13. Tasa KL extendida.**

`LatinonEntropy.latinon_rate_eq_iSup_dyadic`

Dependencias en el registro: 12.

**14. Centro fijo y orden.**

`LatinonEntropy.exists_bounded_latinon_profile_approximation`

Dependencias en el registro: 11, 13.

**15. Regularización y entropía local.**

`LatinonEntropy.finite_rate_latinon_entropy_count`

Dependencias en el registro: 14.

**16. Compacidad de la distancia completa.**

`LatinonEntropy.latinon_full_cut_compact`

Dependencias en el registro: 1.

**17. LDP global.**

`LatinonEntropy.closed_uniform_latinon_upper`

Dependencias en el registro: 13, 15, 16.

**18. Contracción y observables.**

`LatinonEntropy.latinonContractedRate_attained`

Dependencias en el registro: 17.

**19. Densidades,continuidad y normalización.**

`LatinonEntropy.sum_latinonPatternDensity`

Dependencias en el registro: 1.

**20. Puente finito de coordenadas.**

`LatinonEntropy.finite_matrix_pattern_embedding_error`

Dependencias en el registro: 19.

**21. Normalización binomial.**

`LatinonEntropy.standard_pattern_profile_uniform_error`

Dependencias en el registro: 20.

**22. Conteo con restricciones cerradas.**

`LatinonEntropy.finite_rate_standard_pattern_entropy_count`

Dependencias en el registro: 18, 21.

**23. Fórmula logarítmica y fibra vacía.**

`LatinonEntropy.finite_rate_standard_pattern_log_count`

Dependencias en el registro: 22, 16.

## 4. Aplicaciones y ensamblajes de fuentes

El ensamblaje de aplicaciones es `LatinonSeriesApplications.lean`. Contiene las definiciones CDR finitas y el argumento de huella de pares de Wilson, seguido de la correspondencia de factorizaciones, la sustitución de packings, los productos de entropía local y la conservación exacta de tipos. Sus ocho entradas originales se conservan en `lean/evidence/applications`. El ensamblaje central de patrones conserva de forma análoga sus 18 entradas en `lean/evidence/proof-inputs`. Conservar una entrada no afirma que se compile como módulo independiente: los objetivos de compilación son los módulos ensamblados.

**A1.** `finite_rate_factorization_entropy_count`

**A2.** `finite_rate_factorization_pattern_log_count`

**A3.** `replaceSteinerPacking_bicoloured`

**A4.** `wilsonLatinBlockTemplate`

**A5.** `card_restrictedRealizations`

**A6.** `wilson_distinguished_latinon_blocks_entropy_count`

**A7.** `wilson_completed_exact_type_count_eq_base`

**A8.** `residual_subset_completed`

Los resultados CDR cuantifican un sistema base ya completado que contiene el packing distinguido. No deducen la existencia de esa base a partir de solas desigualdades de tamaños de clases. Las familias finales son conjuntos reales de bloques, no copias marcadas. Los cuadrados locales se recuperan de pares fijos fila-columna, por lo que su conteo producto no tiene pérdida de multiplicidad. Los conteos de tipos se refieren a multiconjuntos de colores y coinciden con los de la base; se conservan las configuraciones fijas del residuo, sin afirmar que su número total quede igual.

## 5. Herramientas, imports y reconstrucción

El proyecto entregado fija Lean 4.35.0 y Mathlib en el commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. Su manifiesto fija otros ocho repositorios del ecosistema. La configuración declara 309 raíces de módulos locales, incluidas la entrada canónica y el módulo de consulta de axiomas. La entrada canónica importa la cadena principal mediante el ensamblaje de aplicaciones. El manifiesto de fuentes registra cada módulo seleccionado y su hash. Esta edición no afirma compatibilidad con el snapshot anterior 4.35.0-rc3.

Extraiga el archivo de fuentes de `preprints/LATINON/05_formalization/Latinon_Lean_v1.0.zip`; contiene el directorio de proyecto `lean/` y sus licencias de origen. Instale la herramienta fijada, obtenga los paquetes externos fijados y sus cachés y ejecute desde el proyecto extraído `lake build LatinonFormalization` y `lake env lean ReviewAxioms.lean`, secuencialmente. El primer comando construye la biblioteca configurada de 309 objetivos. La reconstrucción registrada compiló en cambio un objetivo local explícito a la vez. Se conservan sus hashes de fuentes y configuración, los 309 hashes de objetos y los logs de módulos. No se restauró ningún objeto del proyecto; se declara la reutilización de cachés externas.

Los 309 objetivos locales terminaron correctamente el 16 de noviembre de 2026. Las ocho consultas de resultados finales y las tres de tasa buena contienen solo `propext`, `Classical.choice` y `Quot.sound`, sin axiomas matemáticos del proyecto ni `sorryAx`. El verificador de la edición comprueba sus logs conservados contra el archivo y los hashes congelados de fuentes. No ejecuta Lean ni reconstruye paquetes externos.

## 6. Procedencia y límites de la revisión

El identificador del freeze de fuentes es `7b603942c8d078db6c0a5c8729df7012b7786db8`. Sus 309 archivos de módulos y tres archivos de configuración y herramienta tienen los mismos bytes que en la reconstrucción completada. El archivo de fuentes no cambia en esta edición. `preprints/LATINON/02_validation/v1.0/FREEZE.json` registra su SHA-256 y hashes de entradas. Desde la raíz del repositorio, `python scripts/verify_repository.py` comprueba el paquete sin necesitar acceso al repositorio de desarrollo ni a sus objetos Git.

Nueve módulos de grafones provienen del proyecto de Cameron Freer en el commit `9f7be59fa754d260a544b4cfd83d6a5b94f7552e`. El archivo de procedencia conservado enumera los metadatos blueprint retirados y los cambios de compatibilidad. La selección CDR finita proviene de `jtraverso/cdr-palomar-kernel` en el commit `5d1e6fe301e5fc01c92f6145aa34fddfe9c2bd10`. Las definiciones básicas son idénticas byte a byte; se enumeran los cambios de compatibilidad de Wilson y de representación de matrices latinas. Esta selección no importa la antigua biblioteca de existencia por absorción.

La auditoría interna sigue el protocolo del Paper III de CDR en el commit `d12d980f8c86d8795e9faa0c6bb274ee936c7c8e` de la serie. Separa reconstrucción, axiomas, enunciados protegidos, revisión dirigida de pruebas escritas, paridad bilingüe, documentos renderizados e integridad de archivos. La auditoría de la edición es `publication/LATINON_RELEASE_AUDIT.json`. Es una comprobación interna de preparación, no revisión independiente por pares ni certificación exhaustiva de prioridad.