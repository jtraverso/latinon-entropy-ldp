# Companion formal de Conteo de diseños de Steiner con perfiles de color prescritos

Juan Pablo Traverso Gianini

## 1. Enunciados principales

El Teorema 1.1 corresponde a `KqR75.PhysicalCompletion.eventually_designFibre_bilateral` en `R75.lean`. La coloración está fijada y los puntos están etiquetados. La cuota es entera y satisface las ecuaciones de pares sobre la coloración real. La constante de error se fija antes del orden, la coloración y el histograma. Para las cuotas interiores se obtienen la existencia y ambas cotas logarítmicas. La declaración `KqR75.UpperCounting.eventually_card_designFibre_upper_entropy` estima directamente la cardinalidad y por eso admite también fibras vacías.

El Corolario 10.1 corresponde a `KqR75.ProfileLDP.designProfileLDP_probability` en `DesignProfileLDP.lean`. Las proporciones de las clases convergen a límites positivos a lo largo de los órdenes admisibles. Para un cerrado, el teorema admite cualquier número estrictamente inferior a la tasa en todos sus puntos factibles. Para un abierto se fija un punto factible y una tolerancia positiva. Las cotas exponenciales se refieren en ambos casos al cociente entre el número de diseños en el suceso y el número total del mismo orden. La tercera conclusión es la compacidad de los subniveles factibles.

## 2. Correspondencia con las demostraciones

**Secciones 1–2.** Los márgenes se definen en `ExactPairMargins.lean`. La inversa sobre el completo y su norma se estudian en `CompleteJohnson.lean`. El Lema 2.1 aplica `solve_defect` de `HostCorrection.lean` al grafo con aristas retiradas. La corrección simultánea de cargas e histograma se encuentra en `JointCorrection.lean`.

**Sección 3.** El Lema 3.1 se apoya en `SlotPairMargins.affine_spans_kernel`. La realización de la celda sobre los vértices del diseño se verifica en `PhysicalAffineCell.lean`. Las declaraciones `pair_covered_once` y `switch_cell` permiten cambiar el histograma conservando la cobertura.

**Secciones 4–5.** La desigualdad para un bloque está en `SignedBlock.lean`. Tras sumar sobre los bloques disponibles se obtiene la deriva física `energy_drift_rate` de `PhysicalDrift.lean`. Primero se controla la proporción de peso de un tipo y después su número de selecciones. El resultado hasta el horizonte es `eventually_count` en `PhysicalHorizonCounts.lean`.

**Secciones 6–7.** La cobertura de las aristas restantes utiliza `eventually_cover_physical` en `PhysicalCover.lean`. Para el Lema 6.1, `OmniBridge.exists_omni` aplica el resultado importado `RefinedAbsorption.Original2024.theorem_1_7_two_le`; `eventually_absorption_budget` y `physical_completion` dan el grado y la cobertura que necesita el artículo. El Lema 7.1 reúne los prefijos buenos con `corrected_completion` de `CorrectedCompletion.lean`.

**Secciones 8–9.** La recuperación de los bloques elegidos y la cota factorial para la multiplicidad de sus órdenes son `recover_picked` y `order_fibre_card` en `PrefixRecovery.lean`. La cota superior pasa por `UpperWeightedReveal.lean`, `UpperExceptionalWeight.lean` y `UpperEntropyRate.lean`, y admite pesos de tipo nulos.

**Sección 10.** `KqR75.SlotPairMargins.round_quotas` redondea las cuotas conservando sus márgenes. `ProfileTypeLaw.lean` compara las leyes finita y límite. Los controles de conteo, tasa y topología están en `DesignProfileCounts.lean`, `DesignProfileRates.lean` y `ProfileLDPPrinciple.lean`. La equivalencia `orderedMargins_eq_iff` identifica la condición de pares del manuscrito con la de la declaración probabilística final. El ejemplo gráfico y la deducción elemental mediante Pinsker ilustran ese corolario en el texto.

## 3. Fuentes y verificación

El archivo `steiner-profiles-lean.zip` contiene los 162 módulos locales, la configuración de Lake, las revisiones fijadas, los verificadores y sus resultados. La entrada canónica es `Reconstructed` y la versión de Lean es 4.35.0. El kernel cargó 59 importaciones externas desde las dependencias compiladas y verificó 1.997 declaraciones del proyecto. El catálogo imprimió 1.750 registros de teoremas y sus 1.750 pruebas. Hay 1.741 nombres distintos, incluidos lemas privados y teoremas generados. Para cada registro se contrastaron los axiomas con `propext`, `Classical.choice` y `Quot.sound`.

Las firmas y los axiomas están en `verification/THEOREMS.txt`. Los términos de prueba, identificados por módulo y nombre, están en `verification/PROOFS.txt` dentro del ZIP. El archivo comprimido distribuye el catálogo completo de pruebas. Su suma de verificación figura en el `SHA256SUMS` adjunto. Para repetir la comprobación, descomprima el archivo y ejecute desde el directorio `lean`, con acceso a las dependencias fijadas y un directorio de salida nuevo:

```
lake build
lake env python ../verification/recheck.py ../recheck-output
```
